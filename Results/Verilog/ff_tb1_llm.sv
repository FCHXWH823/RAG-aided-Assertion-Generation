module ff_tb1_llm;

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

   // Assertion 1
   assert property (@(posedge clk) 
                    (in == 1'b1) |-> (out == 1'b1) 
                    else (rst == 1'b1));

   // Assertion 2
   assert property (@(posedge clk) 
                    (rst == 1'b1) |-> (out == 1'b0));

   // Assertion 3
   always @(rst) begin  
      assert (rst == 1'b1) |-> (out == 1'b0);      
   end

endmodule