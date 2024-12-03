module fifo_tb4_llm;

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

   // Assertions to check FIFO properties
   // Assertion 1: Check that no write occurs when FIFO is full
   assert property (@(posedge clk) (wr_en && full) |=> $fatal("Write attempted while FIFO is full"));
   
   // Assertion 2: Check that no read occurs when FIFO is empty
   assert property (@(posedge clk) (rd_en && empty) |=> $fatal("Read attempted while FIFO is empty"));

   // Assertion 3: Check that rd_data equals correct_rd_data (first element in FIFO)
   logic [WIDTH-1:0] correct_rd_data; // Assuming correct_rd_data will be assigned appropriately inside DUT
   always_ff @(posedge clk) begin
      if (rd_en && !empty) begin
         assert property (rd_data == correct_rd_data) else $fatal("Wrong data read from FIFO");
      end
   end

endmodule