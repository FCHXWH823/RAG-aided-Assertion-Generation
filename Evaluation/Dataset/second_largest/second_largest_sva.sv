module second_largest_sva #(parameter
  DATA_WIDTH = 32
) (
  input clk,
  input resetn,
  input [DATA_WIDTH-1:0] din,
  input logic [DATA_WIDTH-1:0] dout,
  input logic [DATA_WIDTH-1:0] max_q,
  input logic [DATA_WIDTH-1:0] max2_q
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_max_greater_max2: assert property ( (max_q == 0) | ( max_q > max2_q )); 

endmodule

