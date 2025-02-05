module rounding_division #(parameter
  DIV_LOG2=1,
  OUT_WIDTH=3,
  IN_WIDTH=OUT_WIDTH+DIV_LOG2
) (
  input [IN_WIDTH-1:0] din,
  input clk,
  input rst,
  input logic [OUT_WIDTH-1:0] dout
);

// calculate the expected value for this exercise
longint f_in;
longint f_div;
longint f_pow2;
longint f_res;
wire    f_mod_nz;
wire [OUT_WIDTH-1:0] f_res_w;

assign f_pow2   = ( 1'b1 << DIV_LOG2);
assign f_in     = din;
assign f_mod_nz = (( f_in % f_pow2 ) == 0)? 0 : 1;
assign f_div    = ( f_in /  f_pow2 );
assign f_res    = f_div + f_mod_nz ;
assign f_res_w  = f_res[OUT_WIDTH-1:0];

sva_res_correct: assert property ( dout == f_res_w );

endmodule