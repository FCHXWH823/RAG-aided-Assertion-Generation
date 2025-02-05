module Gray_To_Binary_sva #(
	parameter DATA_WIDTH = 3
) 
(
	input [DATA_WIDTH-1:0]        gray,
	input logic [DATA_WIDTH-1:0] bin,
          input clk,
          input rst
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~rst);

wire [DATA_WIDTH-1:0] gray_f;

// In order to construct our gray code we converter the binary
// gray = bin ^ ( bin >> 1 ) 

assign gray_f = bin ^ ( bin >> 1 );

sva_inv_bin : assert property ( gray_f == gray );

endmodule