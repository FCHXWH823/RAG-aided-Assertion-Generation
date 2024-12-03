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

   // Assertion 1: Check if output is equal to input from one cycle in the past
   assert property (@(posedge clk) (in == $past(out)));

   // Assertion 2: Check that output doesn't change when enable isn't asserted (using $past)
   assert property (@(posedge clk) (!en | (out == $past(out)));

   // Assertion 3: Check that output doesn't change when enable isn't asserted (using $stable)
   assert property (@(posedge clk) (!en | $stable(out)));

   // Assertion 4: Check for asynchronous reset
   always @(rst) #1 assert(out == 1'b0) if (rst == 1'b1);

endmodule