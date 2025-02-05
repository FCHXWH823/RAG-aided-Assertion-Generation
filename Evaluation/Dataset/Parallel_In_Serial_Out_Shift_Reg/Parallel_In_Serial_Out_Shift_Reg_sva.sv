module Parallel_In_Serial_Out_Shift_Reg_sva #(
	parameter DATA_WIDTH = 16
) 
(
	input clk,
	input resetn,
	input [DATA_WIDTH-1:0] din,
	input                  din_en,
	input logic           dout
);

default clocking cb @(posedge clk);
endclocking
default disable iff (~resetn);

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

sva_shift_reg : assert property ( ~v_f_q | ( v_f_q & din_f_q[0] == dout )); 

endmodule