module ff_tb2;

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

   assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));

   
   assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

   always @(rst) #1 assert(out == 1'b0);  
endmodule
