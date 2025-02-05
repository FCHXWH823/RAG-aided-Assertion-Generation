module thermocouple_sva #(localparam clk_freq = 10, localparam CBITS = 5) (input clk, input rst, input spi_not_busy, input [31:0] spi_rx_data, input reg [13:0] tc_temp_data, input reg [11:0] junction_temp_data, input reg [3:0] fault_bits, input logic [1:0] state);
	p1: assert property (@(posedge clk) s_eventually rst || state == 1);
endmodule