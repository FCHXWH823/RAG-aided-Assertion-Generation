module uart_transmit_sva #(localparam d_width = 4, localparam c_width = 3) (input clk, input rst, input tx_ena, input [d_width - 1: 0] tx_data, input reg tx, input reg tx_busy, input reg tx_state);
	
	p1: assert property (@(posedge clk) s_eventually rst == 1 ||  tx_state == 0);
  	// F G (rst = FALSE) -> G F (tx_state = FALSE)
endmodule