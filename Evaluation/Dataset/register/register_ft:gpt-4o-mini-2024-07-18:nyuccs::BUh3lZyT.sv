// Greg Stitt
// University of Florida

// Module: register
// Description: Implements a register with an active high, asynchronous reset
// and an enable signal.

module register
  #(
    parameter WIDTH = 8
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    output logic [WIDTH-1:0] out
    );
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst)
        out <= '0;
      else if (en)
        out <= in;      
   end 
   

assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));
assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));

// assert property (@(posedge clk) disable iff (rst) (@(posedge clk)      // every clock tick     en |=> $past(in)[*0] // enable on current clk allows us to sample last-cycle's in));
// assert property (@(posedge clk) disable iff (rst) (en |=> out == $past(in,1)) iff (@(posedge clk)      // every clock tick     en |=> $past(in)[*0] // enable on current clk allows us to sample last-cycle's in));
assert property (@(posedge clk) disable iff (rst) ((!en) |=> (out ##1 $past(out))));
assert property (@(posedge clk) disable iff (rst) (!en |=> out == $past(out,1)) iff ((!en) |=> (out ##1 $past(out))));

endmodule
