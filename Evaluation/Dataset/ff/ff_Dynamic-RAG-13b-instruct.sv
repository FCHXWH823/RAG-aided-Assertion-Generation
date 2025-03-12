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

assert property (@(posedge clk) disable iff (rst) ($onehot(out ^ $past(in)) |-> en));
assert property (@(posedge clk) disable iff (rst) (en |=> out == $past(in,1)) iff ($onehot(out ^ $past(in)) |-> en));
assert property (@(posedge clk) disable iff (rst) (($stable(out)) |-> ((!en) && $changed(out))));
assert property (@(posedge clk) disable iff (rst) (!en |=> out == $past(out,1)) iff (($stable(out)) |-> ((!en) && $changed(out))));

endmodule
