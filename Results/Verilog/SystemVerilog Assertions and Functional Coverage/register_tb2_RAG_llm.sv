module register_tb2;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;

   logic output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);

         if (first_en) output_check_en = 1'b1;
         if (en) first_en = 1'b1;         
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Assertion 1
   assert property (@(posedge clk) disable iff (rst) (en == 1'b1) |=> (out == in));

   // Assertion 2
   assert property (@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == out[$past(clk)])); // Assuming out[$past(clk)] represents the previous value of out

   // Assertion 3
   assert property (@(posedge clk) disable iff (rst) (en == 1'b0) |=> (out == out[$past(clk)]));

   // Assertion 4
   assert property (@(posedge clk) disable iff (!output_check_en) (en == 1'b1) |=> (out == in[$past(clk)]));

   // Assertion 5
   always @(rst) assert (rst == 1'b1) |=> (out == 0);

endmodule