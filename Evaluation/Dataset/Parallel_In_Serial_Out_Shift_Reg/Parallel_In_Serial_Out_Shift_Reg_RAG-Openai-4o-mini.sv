module Parallel_In_Serial_Out_Shift_Reg #(
	parameter DATA_WIDTH = 16
) 
(
	input clk,
	input resetn,
	input [DATA_WIDTH-1:0] din,
	input                  din_en,
	output logic           dout
);

reg  [DATA_WIDTH-1:0] data_q;
wire [DATA_WIDTH-1:0] data_next;

assign data_next = din_en ? din : data_q >> 1;

always @(posedge clk)
begin
	if( ~resetn) begin
		data_q <= '0;
	end else begin
		data_q <= data_next;
	end
end

assign dout = data_q[0]; 



assert property (@(posedge clk) disable iff (~resetn) (din_en |-> (dout == data_q[0])));
assert property (@(posedge clk) disable iff (~resetn) (~v_f_q | (v_f_q & din_f_q[0] == dout)) iff (din_en |-> (dout == data_q[0])));

endmodule
