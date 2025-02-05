module Gray_Code_Counter_sva #(parameter
  DATA_WIDTH = 4
) (
  input clk,
  input resetn,
  input logic [DATA_WIDTH-1:0] out,
  input unused_bin_inc,
  input logic [DATA_WIDTH-1:0] gray_q,	
  input logic [DATA_WIDTH-1:0] gray_next
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_gray_1_bit_diff : assert property ( unused_bin_inc |  $onehot( gray_next ^ gray_q ) );


endmodule