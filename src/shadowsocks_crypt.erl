-module(shadowsocks_crypt).

%% API
-export([methods/0, init_cipher_info/2, encode/2, decode/2, key_iv_len/1, stream_init/3, hmac/2]).

-include("shadowsocks.hrl").

methods() ->
    [rc4_md5, aes_128_cfb, aes_192_cfb, aes_256_cfb, aead_aes_128_gcm, aead_aes_192_gcm, aead_aes_256_gcm, none].

-record(aead_state, {
          method :: aes_gcm,
          key :: binary(),
          ctr = 0 :: non_neg_integer(),
          chunk :: {ChunkType :: frame_len | frame_data, ChunkLen :: non_neg_integer()}
         }).

%%--------------------------------------------------------------------
%% @doc
%% Return the cipher information
%% 
%% @spec cipher_info(Method, Password::string()) -> #cipher_info{}.
%% 
%%      Method := rc4_md5 | des_cfb |  | aes_cfb128
%% @end
%%--------------------------------------------------------------------
init_cipher_info(none, _) ->
    #cipher_info{method=none};

init_cipher_info(Method, Password) ->
    {KeyLen, IvLen} = key_iv_len(Method),
    {Key, _NewIv} = evp_bytestokey(Password, KeyLen, IvLen),
    %% use another random Iv, but not the one returned from evp_bytestokey()
    NewIv = crypto:strong_rand_bytes(IvLen),
    #cipher_info{method=Method, key=Key, encode_iv=NewIv, decode_iv=undefined,
                stream_enc_state = stream_init(Method, Key, NewIv)}.

%%--------------------------------------------------------------------
%% @doc 
%% Encode function
%% @spec encode(CipherInfo, Data) -> Data
%%      CipherInfo := cipher_info()
%%      Data := iolist() | binary()
%% @end
%%--------------------------------------------------------------------
encode(#cipher_info{method=none}, Data) ->
    Data;

encode(#cipher_info{iv_sent = false, encode_iv=Iv}=CipherInfo, Data) ->
    NewCipherInfo = CipherInfo#cipher_info{iv_sent=true},
    {NewCipherInfo1, EncData} = encode(NewCipherInfo, Data), 
    {NewCipherInfo1, [Iv, EncData]};

encode(#cipher_info{method=rc4_md5, stream_enc_state=S}=CipherInfo, Data) ->
    {S1, EncData} = crypto:stream_encrypt(S, Data),
    {CipherInfo#cipher_info{stream_enc_state=S1}, EncData};

encode(#cipher_info{stream_enc_state=(#aead_state{}=State)}=CipherInfo, Data) ->
    {NewState, ResData} = encode_aead(State, Data, iolist_size(Data), []),
    {CipherInfo#cipher_info{stream_enc_state=NewState}, ResData};

encode(#cipher_info{method=Method, key=Key, encode_iv=Iv, enc_rest=Rest}=CipherInfo, IoData)
  when Method =:= aes_128_cfb; Method =:= aes_192_cfb; Method =:= aes_256_cfb ->
    Data = iolist_to_binary(IoData),
    DataSize = size(Data),
    RestSize = size(Rest),
    BufLen = (DataSize+RestSize) div 16 * 16,
    
    <<Data2:BufLen/binary, Rest2/binary>> = <<Rest/binary, Data/binary>>,
    EncData = crypto:block_encrypt(aes_cfb128, Key, Iv, Data2),
    NewIv = binary:part(<<Iv/binary, EncData/binary>>, size(EncData)+16, -16),
    EncRest = crypto:block_encrypt(aes_cfb128, Key, NewIv, Rest2),
    Result = binary:part(<<EncData/binary, EncRest/binary>>, RestSize, DataSize),
    {CipherInfo#cipher_info{encode_iv=NewIv, enc_rest=Rest2}, Result}.

encode_aead(State, _Data, Len, ResDataAcc) when Len =:= 0 ->
    {State, ResDataAcc};
encode_aead(State, Data, Len, ResDataAcc) ->
    {ChunkData, ChunkLen, RestData} =
        case Len of
            _ when Len > 16#4000 ->
                << LongChunkData:16#3FFF/binary, LongRestData/binary >> = iolist_to_binary(Data),
                {LongChunkData, 16#3FFF, LongRestData};
            _ ->
                {Data, Len, undefined}
        end,
    #aead_state{method=Method, key=Key, ctr=Ctr}=State,
    {EncLen, EncLenTag} = crypto:block_encrypt(Method, Key, aead_nonce(Ctr), {<<>>, << 0:2, Len:14 >>, ?AEAD_TAG_LEN}),
    {EncData, EncDataTag} = crypto:block_encrypt(Method, Key, aead_nonce(Ctr+1), {<<>>, ChunkData, ?AEAD_TAG_LEN}),
    encode_aead(State#aead_state{ctr=Ctr+2}, RestData, Len - ChunkLen, [ResDataAcc, EncLen, EncLenTag, EncData, EncDataTag]).


%%--------------------------------------------------------------------
%% @doc 
%% Decode function
%% @spec decode(CipherInfo, Data) -> Data
%%      CipherInfo := {default, EncTable::list(), DecTable::list()} |
%%                    {Method, Key::binary(), Iv::binary()}
%%      Method := default | rc4 | des_cfb
%%      Data := iolist() | binary()
%% @end
%%--------------------------------------------------------------------
decode(#cipher_info{method=none}, Data) ->
    Data;

%% recv iv
decode(CipherInfo=#cipher_info{method=M, decode_iv=undefined, dec_rest={Rest, _RestSize}}, EncData) ->
    {_, IvLen} = key_iv_len(M),
    case <<Rest/binary, EncData/binary>> of
        Rest1 when byte_size(Rest1) >= IvLen ->
            <<Iv:IvLen/binary, Rest2/binary>> = Rest1,
            StreamState = shadowsocks_crypt:stream_init(M, CipherInfo#cipher_info.key, Iv),
            decode(CipherInfo#cipher_info{decode_iv=Iv, stream_dec_state=StreamState, dec_rest = {<<>>, 0}}, Rest2);
        Rest1 ->
            {CipherInfo#cipher_info{dec_rest={Rest1, byte_size(Rest1)}}}
    end;

decode(#cipher_info{method=rc4_md5, stream_dec_state=S}=CipherInfo, EncData) ->
    {S1, Data} = crypto:stream_decrypt(S, EncData),
    {CipherInfo#cipher_info{stream_dec_state=S1}, Data};

decode(#cipher_info{stream_dec_state=(#aead_state{}=State), dec_rest={Acc, AccSize}}=CipherInfo, Data) ->
    {NewState, NewAccTuple, ResData} = decode_aead(State, [Acc, Data], AccSize + iolist_size(Data), <<>>),
    {CipherInfo#cipher_info{stream_dec_state=NewState, dec_rest=NewAccTuple}, ResData};

decode(#cipher_info{method=Method, key=Key, decode_iv=Iv, dec_rest={Rest, RestSize}}=CipherInfo, EncIoData)
  when Method =:= aes_128_cfb; Method =:= aes_192_cfb; Method =:= aes_256_cfb ->
    EncData = iolist_to_binary(EncIoData),
    DataSize = size(EncData),
    BufLen = (DataSize+RestSize) div 16 * 16,
    <<EncData2:BufLen/binary, Rest2/binary>> = <<Rest/binary, EncData/binary>>,

    Data = crypto:block_decrypt(aes_cfb128, Key, Iv, EncData2),
    NewIv = binary:part(<<Iv/binary, EncData2/binary>>, size(EncData2)+16, -16),
    DecRest = crypto:block_decrypt(aes_cfb128, Key, NewIv, Rest2),
    Result = binary:part(<<Data/binary, DecRest/binary>>, RestSize, DataSize),

    {CipherInfo#cipher_info{decode_iv=NewIv, dec_rest={Rest2, byte_size(Rest2)}}, Result}.

decode_aead(#aead_state{chunk={_, ChunkDataSize}}=State, Acc, AccSize, ResDataAcc)
  when AccSize < (ChunkDataSize + ?AEAD_TAG_LEN) ->
    {State, {Acc, AccSize},  ResDataAcc};

decode_aead(State, Acc, _AccSize, ResDataAcc) ->
    #aead_state{key=Key, ctr=Ctr, chunk={_, ChunkDataSize}} = State,
    << EncChunkData:ChunkDataSize/binary, ChunkTag:?AEAD_TAG_LEN/binary, NewAcc/binary >> = iolist_to_binary(Acc),
    case crypto:block_decrypt(aes_gcm, Key, aead_nonce(Ctr), {<<>>, EncChunkData, ChunkTag}) of
        error ->
            exit(decrypt_error);
        ChunkData ->
            {NewState, ResData} = decode_aead_chunk(State#aead_state{ctr=Ctr+1}, ChunkData),
            decode_aead(NewState, NewAcc, byte_size(NewAcc), [ResDataAcc, ResData])
    end.

decode_aead_chunk(#aead_state{chunk={frame_len, _}}=State, ChunkData) ->
    << 0:2, FrameDataSize:14 >> = ChunkData,
    {State#aead_state{chunk={frame_data, FrameDataSize}}, <<>>};
decode_aead_chunk(#aead_state{chunk={frame_data, _}}=State, ChunkData) ->
    {State#aead_state{chunk={frame_len, 2}}, ChunkData}.

hmac(Key, Data) ->
    crypto:hmac(sha, Key, Data, ?HMAC_LEN).

%%--------------------------------------------------------------------
%% @doc 
%% Creates a key and an IV for doing encryption, from a password, 
%% using a hashing function.
%% @spec evp_bytestokey(HashMethod::hash_method(), Password::string(), 
%%                      KeyLen::integer(), IvLen::integer()) ->
%%      {Key::binary(), Iv::binary()}
%% @end
%%--------------------------------------------------------------------
evp_bytestokey(Password, KeyLen, IvLen) ->
    evp_bytestokey_aux(list_to_binary(Password), KeyLen, IvLen, <<>>).

evp_bytestokey_aux(_, KeyLen, IvLen, Acc) when KeyLen + IvLen =< size(Acc) ->
    <<Key:KeyLen/binary, Iv:IvLen/binary, _/binary>> = Acc,
    {Key, Iv};

evp_bytestokey_aux(Password, KeyLen, IvLen, Acc) ->
    Digest = crypto:hash(md5, <<Acc/binary, Password/binary>>),
    NewAcc = <<Acc/binary, Digest/binary>>,
    evp_bytestokey_aux(Password, KeyLen, IvLen, NewAcc).

aead_nonce(Ctr) when Ctr < (1 bsl (?AEAD_NONCE_LEN * 8)) ->
    << Ctr:(?AEAD_NONCE_LEN * 8)/little >>.

key_iv_len(none) ->
    {0, 0};
key_iv_len(rc4_md5) ->
    {16, 16};
key_iv_len(aead_aes_128_gcm) ->
    {16, 16};
key_iv_len(aead_aes_192_gcm) ->
    {24, 24};
key_iv_len(aead_aes_256_gcm) ->
    {32, 32};
key_iv_len(aes_128_cfb) ->
    {16, 16};
key_iv_len(aes_192_cfb) ->
    {24, 16};
key_iv_len(aes_256_cfb) ->
    {32, 16};
key_iv_len(chacha20) ->
    {32, 8}.


stream_init(Method, Key, Iv)
  when Method =:= aead_aes_128_gcm; Method =:= aead_aes_192_gcm; Method =:= aead_aes_256_gcm ->
    AeadKey = hkdf:expand(sha, hkdf:extract(sha, Iv, Key), <<"ss-subkey">>, byte_size(Key)),
    #aead_state{method=aes_gcm, key=AeadKey, ctr=0, chunk={frame_len, 2}};
stream_init(rc4_md5, Key, Iv) ->
    crypto:stream_init(rc4, crypto:hash(md5, <<Key/binary, Iv/binary>>));
stream_init(_, _, _) ->
    undefined.

%% 测试
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

rc4_test() ->

    Cipher = init_cipher_info(aes_128_cfb, "xx"),
    Data1 = <<"hello world">>,
    Data2 = <<"baby">>,
    {Cipher1, EnData1} = encode(Cipher, Data1),
    {Cipher2, EnData2} = encode(Cipher1, Data2),
    IV = Cipher1#cipher_info.encode_iv,
    {Cipher3, <<_IV:16/binary, DeData1/binary>>} = decode(Cipher1#cipher_info{decode_iv=IV}, EnData1),
    {_,       DeData2} = decode(Cipher3, EnData2),
    io:format("~p~n", [DeData1]),
    {0,11} = binary:match(Data1, [DeData1],[]),
    {0,4}  = binary:match(Data2, [DeData2],[]),
    ok.
-endif.
