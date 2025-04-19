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



reg  v_f_q;
wire v_f_next;
reg  [DATA_WIDTH-1:0] din_f_q;
wire [DATA_WIDTH-1:0] din_f_next;
assign din_f_next = { 1'b0 , din_f_q[7:1] };
assign v_f_next   = resetn & din_en;

always @(posedge clk)
begin
	din_f_q <= ~resetn ? {DATA_WIDTH{1'bx}} : 
					din_en ? din : din_f_next; 
	v_f_q   <= v_f_next;
end
assert property(@(posedge clk) disable iff (~resetn) ~v_f_q | (v_f_q & din_f_q[0] == dout));

assert property (@(posedge clk) disable iff (~resetn) ((~v_f_q && v_f_next) |=> (data_q[0] == dout)));
assert property (@(posedge clk) disable iff (~resetn) (~v_f_q | (v_f_q & din_f_q[0] == dout)) iff ((~v_f_q && v_f_next) |=> (data_q[0] == dout)));

endmodule
