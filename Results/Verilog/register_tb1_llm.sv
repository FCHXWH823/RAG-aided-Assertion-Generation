module register_tb1_llm;

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

   // Assertion 1: Check that out equals in on posedge clk when rst is 0
   assert property (@(posedge clk) (rst == 0) |=> (out == in))
      else $fatal("Assertion failed: Output does not match input when rst is 0");

   // Assertion 2: Check that out equals in on posedge clk when rst is 0
   assert property (@(posedge clk) (rst == 0) |=> (out == in))
      else $fatal("Assertion failed: Output does not match input when rst is 0");

   // Assertion 3: Check that out equals 0 on posedge clk when rst is 1
   assert property (@(posedge clk) (rst == 1) |=> (out == 0))
      else $fatal("Assertion failed: Output is not 0 when rst is 1");

   // Assertion 4: Immediate assertion checking out equals 0 when rst is 1
   always @(rst) assert (rst == 1 -> out == 0) 
      else $fatal("Immediate Assertion failed: Output is not 0 when rst is 1");

endmodule