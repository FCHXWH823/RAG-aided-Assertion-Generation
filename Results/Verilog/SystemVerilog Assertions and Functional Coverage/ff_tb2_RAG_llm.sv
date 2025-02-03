module ff_tb2;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.*);

   initial begin : generate_clock
      while(1)
        #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Assertions
   initial begin
      // Assertion 1: If en is true at the posedge of clk, then out must equal in from one cycle ago.
      assert property (@(posedge clk) disable iff (rst) (en == 1'b1) |=> (out == in)) 
         else $fatal("Assertion 1 failed: out does not match in when en is true.");

      // Assertion 2: If en is false at the posedge of clk, then out must remain the same as one cycle ago.
      assert property (@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == $past(out))) 
         else $fatal("Assertion 2 failed: out does not remain the same when en is false.");

      // Assertion 3: If en is false at the posedge of clk, out must remain stable in the next cycle.
      assert property (@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == $past(out))) 
         else $fatal("Assertion 3 failed: out does not remain stable when en is false.");

      // Assertion 4: When rst is high, out must be 0.
      always @(rst) 
         assert (rst == 1'b1) |=> (out == 1'b0) 
         else $fatal("Assertion 4 failed: out is not 0 when rst is high.");
   end

endmodule