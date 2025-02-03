module ff_tb1_RAG_llm;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.en(1'b1), .*);

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

   // Assertion 1: Ensures that out is true in the next clock cycle if in is true at posedge clk, disabled when rst is asserted
   assert property(@(posedge clk) disable iff (rst) (in |=> out));

   // Assertion 2: Ensures that out is false in the next clock cycle if rst is true at posedge clk
   assert property(@(posedge clk) (rst |=> !out));

   // Assertion 3: Ensures that out is false immediately after any event on the reset signal rst
   always @(rst) begin  
      assert(out == 1'b0);      
   end

endmodule