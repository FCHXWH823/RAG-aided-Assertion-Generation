module mux2x1_tb;

   logic in0, in1, sel;
   
   logic out_assign, out_if, out_if2, out_case;   

   localparam period = 20;
   
   mux2x1_assign DUT_ASSIGN (.out(out_assign), .*);
   mux2x1_if DUT_IF (.out(out_if), .*);
   mux2x1_if2 DUT_IF2 (.out(out_if2), .*);
   mux2x1_case DUT_CASE (.out(out_case), .*);

   // Immediate assertion to check if the output of DUT_ASSIGN equals the expected output
   always_comb begin
       // Assuming 'correct' is defined or calculated based on inputs in0, in1, and sel
       logic correct = (sel) ? in1 : in0; // Example logic for expected output

       assert (out_assign == correct) else
           $fatal("Assertion failed: out_assign does not equal correct");
   end

endmodule