module mux2x1_tb;

   logic in0, in1, sel;
   
   logic out_assign, out_if, out_if2, out_case;   

   localparam period = 20;
   
   mux2x1_assign DUT_ASSIGN (.out(out_assign), .*);
   mux2x1_if DUT_IF (.out(out_if), .*);
   mux2x1_if2 DUT_IF2 (.out(out_if2), .*);
   mux2x1_case DUT_CASE (.out(out_case), .*);

   function void check_output(string name, logic actual, logic correct);

      assert(actual == correct) else $error("ERROR at time %0t: %s = %b instead of %d.", $realtime, name, actual, correct);               

   endfunction

   logic correct_output;           

   initial
     begin
        $timeformat(-9, 0, " ns");
        
        for (integer i=0; i < 8; i = i+1) begin
           
           in0 = i[0];
           in1 = i[1];
           sel = i[2];

           #period;

           correct_output = sel ? in1 : in0;
           check_output("out_assign", out_assign, correct_output);
           check_output("out_if", out_if, correct_output);
           check_output("out_if2", out_if2, correct_output);
           check_output("out_case", out_case, correct_output);
        end        
     end 
endmodule