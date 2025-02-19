module Programmable_Sequence_Detector 
#(
	parameter SEQ_W = 5
)
(
  input clk,
  input resetn,
  input [SEQ_W-1:0] init,
  input             din,
  input logic      seen
);

reg  [SEQ_W-1:0] seq_q;
wire [SEQ_W-1:0] seq_next;

assign seq_next = { seq_q[SEQ_W-2:0] , din } ;

always @(posedge clk) 
begin
	if ( ~resetn ) begin
		seq_q <= '0;
	end else begin
		seq_q <= seq_next;
	end
end

assign seen = seq_q == init;


assert property(@(posedge clk) disable iff(~resetn) seen == (seq_q == init));

// assert property (@(posedge clk) default disable iff (~resetn) (seen == (seq_q == init)));
// assert property (@(posedge clk) default disable iff (~resetn) (seen == (seq_q == init)) iff (seen == (seq_q == init)));

endmodule
