module ff_tb1;

   localparam NUM_TESTS = 10000;   
   logic clk=1'b0, rst, en, in, out;

   ff DUT (.en(1'b1), .in(in), .out(out), .rst(rst));

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

   // Assertion 1: out must be true in the following clock cycle if in is true on the posedge of clk, disabled when rst is asserted.
   assert property (@(posedge clk) disable iff (rst) (in -> out));

   // Assertion 2: out must be false in the following clock cycle if rst is true on the posedge of clk.
   assert property (@(posedge clk) (rst -> !out));

   // Assertion 3: out must be false (1'b0) immediately after any event on the reset signal (rst).
   always @(rst) begin  
      assert(out == 1'b0);      
   end

endmodule