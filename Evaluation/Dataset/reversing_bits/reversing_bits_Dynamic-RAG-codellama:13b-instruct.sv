module reversing_bits #(
	parameter DATA_WIDTH=3
) 
(
  input clk,
  input rst,
  input  [DATA_WIDTH-1:0]       din,
  output logic [DATA_WIDTH-1:0] dout
);

genvar i;
generate;
	for (i=0; i<DATA_WIDTH; i++) begin
		assign dout[i] = din[DATA_WIDTH-i-1];
	end
endgenerate


assert property(@(posedge clk) disable iff (~rst) dout[0] == din[DATA_WIDTH-1]);

assert property (@(posedge clk) disable iff (~rst) (dout[0] == din[data_width-1]));
assert property (@(posedge clk) disable iff (~rst) (dout[0] == din[DATA_WIDTH-1]) iff (dout[0] == din[data_width-1]));

endmodule
