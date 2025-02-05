module VGA_sva #(localparam  size = 1, localparam h_bits = 7, localparam v_bits = 5) (input clk, input rst, input reg disp_ena, input reg n_blank, input reg n_sync, input reg [h_bits-1:0] col, input reg [v_bits-1:0] row);

	
	p1: assert property  (@(posedge clk) s_eventually rst == 1 || disp_ena == 1);
  	// F G !rst -> G F disp_ena
endmodule
