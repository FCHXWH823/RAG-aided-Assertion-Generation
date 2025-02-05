module lcd_sva #(parameter clk_freq = 1, parameter CBITS = 9) (input clk, input [6:0] in_data, input lcd_enable, input [9:0] lcd_bus, input logic e, input logic[7:0] lcd_data, input logic rw, input logic rs, input logic busy, input logic [1:0] state);
	p1: assert property (@(posedge clk) s_eventually (lcd_enable == 0 || state == 2));
endmodule