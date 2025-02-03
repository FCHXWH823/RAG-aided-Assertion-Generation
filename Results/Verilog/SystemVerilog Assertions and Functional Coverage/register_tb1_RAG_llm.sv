module register_tb1;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) DUT (.en(1'b1), .in(in), .out(out));

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b1;

      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         @(posedge clk);
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Assertion 1: Ensure output matches input from the previous clock cycle if reset is not active.
   assert property (@(posedge clk) disable iff (rst) (out == $past(in, 1)));

   // Assertion 2: Verify that if reset is not asserted, output should match input from the previous cycle.
   assert property (@(posedge clk) (rst == 1'b0) |-> (out == $past(in, 1)));

   // Assertion 3: Check that if reset is asserted, output should be reset to zero in the next clock cycle.
   assert property (@(posedge clk) (rst == 1'b1) |-> (out == 0));

   // Assertion 4: Immediate assertion to check if out equals 0 when rst equals 1.
   always @(rst) assert (rst == 1'b1) |-> (out == 0);

endmodule