module fifo_tb1;

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
      $display("Tests Completed.");      
   end // initial begin

   // Assertion 1:
   // Ensures that a write operation cannot occur when the FIFO is full.
   always @(posedge clk) begin
      assert(!wr_en || !full) else $fatal("Write operation cannot occur when FIFO is full.");
   end 

   // Assertion 2:
   // Ensures that a read operation cannot occur when the FIFO is empty.
   always @(posedge clk) begin
      assert(!rd_en || !empty) else $fatal("Read operation cannot occur when FIFO is empty.");
   end 

   // Assertion 3:
   // Checks that DUT.valid_wr and full cannot be 1 at the same time.
   assert property (@(posedge clk) (DUT.valid_wr == 1) |-> (full == 0));

   // Assertion 4:
   // Checks that DUT.valid_rd and empty cannot be 1 at the same time.
   assert property (@(posedge clk) (DUT.valid_rd == 1) |-> (empty == 0));

   // Assertion 5:
   // Checks that if a write operation is valid, then the FIFO should not be full.
   assert property (@(posedge clk) (DUT.valid_wr == 1) |-> (full == 0));

   // Assertion 6:
   // Checks that if a read operation is valid, then the FIFO should not be empty.
   assert property (@(posedge clk) (DUT.valid_rd == 1) |-> (empty == 0));

endmodule