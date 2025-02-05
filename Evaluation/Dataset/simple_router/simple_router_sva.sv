module simple_router_sva #(
	parameter DATA_WIDTH = 32
) (
  input  rst,
  input  clk,
  input  [DATA_WIDTH-1:0] din,
  input  din_en,
  input  [1:0] addr,
  input logic [DATA_WIDTH-1:0] dout0,
  input logic [DATA_WIDTH-1:0] dout1,
  input logic [DATA_WIDTH-1:0] dout2,
  input logic [DATA_WIDTH-1:0] dout3
);

dout_zero_din_en_false: assert property (din_en | ((dout0 == 0) & (dout1 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr0_match: assert property ((~(din_en & (addr == 2'd0))) | ((dout0 == din) & (dout1 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr1_match: assert property ((~(din_en & (addr == 2'd1))) | ((dout1 == din) & (dout0 == 0) & (dout2 == 0) & (dout3 == 0)));
dout_addr2_match: assert property ((~(din_en & (addr == 2'd2))) | ((dout2 == din) & (dout0 == 0) & (dout1 == 0) & (dout3 == 0)));
dout_addr3_match: assert property ((~(din_en & (addr == 2'd3))) | ((dout3 == din) & (dout0 == 0) & (dout1 == 0) & (dout2 == 0)));

endmodule