module i2c_sva #(parameter divider = 125, parameter CBITS = 9) (input clk, input rst, input scl_not_ena, input logic data_clk, input logic stretch);

	p1: assert property (@(posedge clk) s_eventually rst == 1 || scl_not_ena == 1 || stretch == 1);

endmodule