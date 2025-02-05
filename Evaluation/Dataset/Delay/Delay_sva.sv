module Delay_sva
#(
          parameter N = 750, 
          parameter CBITS = 10
) 
(input clk, input rst, input logic sig);

p1: assert property (@(posedge clk) s_eventually (rst || sig == 1)) ;
endmodule