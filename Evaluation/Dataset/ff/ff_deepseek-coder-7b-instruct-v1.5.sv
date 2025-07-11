module ff
  (
   input logic clk, rst, en, in,
   output logic out   
   );

   always_ff @(posedge clk or posedge rst)
      if (rst) out = 1'b0;
      else if (en) out = in;         

assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));
assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));

assert property (@(posedge clk) disable iff (rst) (out == $past(in, 1)));
assert property (@(posedge clk) disable iff (rst) (en |=> out == $past(in,1)) iff (out == $past(in, 1)));
assert property (@(posedge clk) disable iff (rst) (!$rose(en) |-> $stable(out)));
assert property (@(posedge clk) disable iff (rst) (!en |=> out == $past(out,1)) iff (!$rose(en) |-> $stable(out)));

endmodule
