module PWM_sva #(parameter CBITS = 10) 
(
          input clk,
          input rst, 
          input [3:0] sw, 
          input logic pulse
);

p1: assert property (@(posedge clk) (1 |-> s_eventually(~pulse)));

endmodule

