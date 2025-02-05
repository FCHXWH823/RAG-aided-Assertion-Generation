module Programmable_Sequence_Detector_sva 
#(
	parameter SEQ_W = 5
)
(
  input clk,
  input resetn,
  input [SEQ_W-1:0] init,
  input             din,
  input logic      seen,
  input logic  [SEQ_W-1:0] seq_q
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

sva_seen : assert property ( seen == ( seq_q == init ));

endmodule