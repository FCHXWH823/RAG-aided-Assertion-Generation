module ff_tb1;

   localparam NUM_TESTS = 10000;   
   logic clk = 1'b0, rst, en, in, out;

   ff DUT (.en(1'b1), .rst(rst), .in(in), .out(out));

   initial begin : generate_clock
      while(1)
        #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, "" ns"");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;

      for (int i = 0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i = 0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display(""Tests completed."");
   end 

   // Assertion 1: Check that whenever the signal in is true on a clock cycle,
   // the signal out must be true in the following clock cycle, evaluated on rising edge of clk,
   // disabled when rst is high.
   assert property (@(posedge clk) disable iff (rst) (in == 1'b1) |=> (out == 1'b1));

   // Assertion 2: Check that out is not asserted on every rising edge after rst is 1.
   assert property (@(posedge clk) disable iff (rst) (rst == 1'b0) |=> (out == 1'b1));

   // Assertion 3: Check for the asynchronous reset, when rst is 1, out signal should be 0.
   always @(rst) begin  
      assert (rst == 1'b1) |=> (out == 1'b0);      
   end

endmodule