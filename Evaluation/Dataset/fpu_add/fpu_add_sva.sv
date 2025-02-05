
module fpu_add_sva(

input           clk,
input           rst,
input           enable,
input   [63:0]  opa, opb,
input          sign,
input  [55:0]  sum_2,
input  [10:0]  exponent_2,

input   [10:0] exponent_a,
input   [10:0] exponent_b,
input   [51:0] mantissa_a,
input   [51:0] mantissa_b,
input   expa_gt_expb,
input   [10:0] exponent_small,
input   [10:0] exponent_large,
input   [51:0] mantissa_small,
input   [51:0] mantissa_large,
input   small_is_denorm,
input   large_is_denorm,
input   large_norm_small_denorm,
input   [10:0] exponent_diff,
input   [55:0] large_add,
input   [55:0] small_add,
input   [55:0] small_shift,
input   small_shift_nonzero ,
input    small_is_nonzero ,
input   small_fraction_enable ,
input   [55:0] small_shift_2,
input   [55:0] small_shift_3,
input   [55:0] sum,
input   sum_overflow, // sum[55] will be 0 if there was no carry from adding the 2 numbers
input   [10:0] exponent,
input   sum_leading_one , // this is where the leading one resides, unless denorm
input   denorm_to_norm
);

property a81;
@(posedge clk) (opa[8] == 1 & enable == 1) |=> (sign == 0);
endproperty
assert_a81: assert property(a81);

property a94;
@(posedge clk) (enable == 0 & opa[5] == 1 & opa[19] == 1 & opa[1] == 0 & opa[4] == 0 & opa[8] == 0) |=> (sign == 1);
endproperty
assert_a94: assert property(a94);

property a107;
@(posedge clk) (enable == 0 & opa[6] == 1 & opa[21] == 1 & opa[7] == 1 & opa[3] == 1 & opa[12] == 1) |=> (sign == 1);
endproperty
assert_a107: assert property(a107);

endmodule