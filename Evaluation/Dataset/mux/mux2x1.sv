"// Greg Stitt
// University of Florida

// Module: mux2x1_assign
// Description: behavioral 2x1 mux using an assign statement.

module mux2x1_assign 
  (
   input logic 	in0,
   input logic 	in1,
   input logic 	sel,
   output logic out
   );

   assign out = sel == 1'b1 ? in1 : in0;

endmodule // mux2x1_assign

module mux2x1
  (
   input logic 	in0,
   input logic 	in1,
   input logic 	sel,
   output logic out
   );

   mux2x1_assign mux (.*);   
endmodule // mux2x1"

