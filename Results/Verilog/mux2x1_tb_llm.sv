module mux2x1_tb;

   logic in0, in1, sel;
   logic out_assign, out_if, out_if2, out_case;   
   localparam period = 20;

   mux2x1_assign DUT_ASSIGN (.out(out_assign), .*);
   mux2x1_if DUT_IF (.out(out_if), .*);
   mux2x1_if2 DUT_IF2 (.out(out_if2), .*);
   mux2x1_case DUT_CASE (.out(out_case), .*);

// Testbench process
   initial begin
       // Initialize inputs
       in0 = 0;
       in1 = 0;
       sel = 0;

       // Wait for the first period
       #period;

       // Apply test vectors
       in0 = 1; in1 = 0; sel = 0;  // Select input 0
       #period;

       // Assertion 1: Check output of assign mux
       assert (out_assign == in0) else $fatal("Error: out_assign does not match expected value.");

       // Change selection to input 1
       in0 = 0; in1 = 1; sel = 1;  
       #period;

       // Assertion 2: Check output of assign mux after input changes
       assert (out_assign == in1) else $fatal("Error: out_assign does not match expected value after input change.");

       // Repeat similar steps for other DUTs and assertions
       // For DUT_IF
       assert (out_if == (sel ? in1 : in0)) else $fatal("DUT_IF Error: Output does not match expected value based on selection.");

       // For DUT_IF2
       assert (out_if2 == (sel ? in1 : in0)) else $fatal("DUT_IF2 Error: Output does not match expected value based on selection.");

       // For DUT_CASE
       assert (out_case == (sel ? in1 : in0)) else $fatal("DUT_CASE Error: Output does not match expected value based on selection.");

       // End simulation after all tests
       #period;
       $finish;
   end

endmodule