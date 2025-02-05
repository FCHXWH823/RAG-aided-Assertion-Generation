module reversing_bits_sva #(
	parameter DATA_WIDTH=3
) 
(
  input  [DATA_WIDTH-1:0]       din,
  input logic [DATA_WIDTH-1:0] dout,
  input clk,
  input rst
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

sva_rev : assert property ( dout[0]  == din[DATA_WIDTH-1]);

endmodule