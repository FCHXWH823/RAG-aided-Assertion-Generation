module register_tb1_RAG_llm;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;
   
   register #(.WIDTH(WIDTH)) DUT (.en(1'b1), .in(in), .out(out), .rst(rst));

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

   // Assertion 1: Check output equals input when rst is 0 at posedge clk
   assert property (@(posedge clk) (rst == 0) |-> (out === in)) 
      else $fatal("Assertion 1 failed: Output does not equal input when rst is 0.");

   // Assertion 2: Repeat check for cases where rst is 0 at posedge clk
   assert property (@(posedge clk) (rst == 0) |-> (out === in)) 
      else $fatal("Assertion 2 failed: Output does not equal input when rst is 0.");

   // Assertion 3: Check output equals 0 when rst is 1 at posedge clk
   assert property (@(posedge clk) (rst == 1) |-> (out === 0)) 
      else $fatal("Assertion 3 failed: Output is not 0 when rst is 1.");

   // Assertion 4: Immediate assertion in an always block for rst equals 1
   always @(rst) 
      assert (rst == 1 -> out === 0) 
      else $fatal("Assertion 4 failed: Output is not 0 when rst is 1.");

endmodule