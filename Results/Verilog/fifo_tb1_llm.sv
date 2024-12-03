module fifo_tb1_llm;

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
      $display(""Tests Completed."");      
   end // initial begin

   // Assertion 1: Check that when clk is at posedge, there is never a write while the FIFO is full
   always @(posedge clk) begin
      assert (!(wr_en && full)) else $fatal(""Write attempted when FIFO is full."");
   end

   // Assertion 2: Check that when clk is at posedge, there is never a read while the FIFO is empty
   always @(posedge clk) begin
      assert (!(rd_en && empty)) else $fatal(""Read attempted when FIFO is empty."");
   end 

   // Assertion 3: Check that DUT.valid_wr and full cannot be 1 at the same time
   assert property (@(posedge clk) (DUT.valid_wr == 1'b1) |-> (full == 1'b0));

   // Assertion 4: Check that DUT.valid_rd and empty cannot be 1 at the same time
   assert property (@(posedge clk) (DUT.valid_rd == 1'b1) |-> (empty == 1'b0));

   // Assertion 5: Check that if DUT.valid_wr is high, full must be 0
   assert property (@(posedge clk) (DUT.valid_wr == 1'b1) |-> (full == 1'b0));

   // Assertion 6: Check that if DUT.valid_rd is high, empty must be 0
   assert property (@(posedge clk) (DUT.valid_rd == 1'b1) |-> (empty == 1'b0));

endmodule