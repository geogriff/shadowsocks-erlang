%% flow event
%%      report: {report, Port, Download, Upload}
%% 
-define(FLOW_EVENT, sserl_flow_event).

%% stat event
%%      new listener {listener, new, Port}
%%      accept  : {listener, accept, Addr, Port}
%%      new conn: {conn, new, Addr, Port}
%% 
-define(STAT_EVENT, sserl_stat_event).

