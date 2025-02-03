module fifo_tb2;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);        
      end

      disable generate_clock;
      $display("Tests Completed.");      
   end  

   // Assertion 1
   assert property (@(posedge clk) (wr_en && !full) |-> !full);
   
   // Assertion 2
   assert property (@(posedge clk) (rd_en && !empty) |-> !empty);
   
   // Assertion 3
   assert property (@(posedge clk) 
      (wr_en && !full) |-> 
      (wr_data == DUT.wr_data) ##[1:$] (rd_en && !empty) |-> (rd_data == wr_data)
   ) else $display("Data integrity check failed: expected=%0d, got=%0d", wr_data, rd_data);

endmodule