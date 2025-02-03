module ff_tb2_RAG_llm;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.*);

   initial begin : generate_clock
      while(1)
        #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

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
      $display(""Tests completed."");
   end 

   // Assertion 1: If en is true at posedge clk, out must equal in from one clock cycle ago.
   assert property(@(posedge clk) disable iff (rst) (en == 1'b1) |=> (out == $past(in)));

   // Assertion 2: If en is false at posedge clk, out must remain the same as it was one clock cycle ago.
   assert property(@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == $past(out)));

   // Assertion 3: If en is false at posedge clk, out must remain stable in the next clock cycle.
   assert property(@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == $past(out)));

   // Assertion 4: When reset is high, out must be 0.
   always @(rst) assert (rst == 1'b1) |=> (out == 1'b0);

endmodule