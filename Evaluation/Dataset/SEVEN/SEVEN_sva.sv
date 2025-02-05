module SEVEN_sva #(parameter freq = 250, parameter CBITS = 8) (input clk, input rst, input [13:0] both7seg, input logic[6:0] segment, input logic digit_select);
	p1: assert property (@(posedge clk) s_eventually rst == 1 || digit_select == 1);
	p2: assert property (@(posedge clk) s_eventually rst == 1 || digit_select == 0);
endmodule