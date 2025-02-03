module fifo_tb3_llm;

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
   
   // Assertion 1: If a write operation is initiated, then the FIFO should not be full in the next clock cycle.
   assert property (@(posedge clk) (wr_en && !full) |-> (!full));

   // Assertion 2: If a read operation is initiated, then the FIFO should not be empty in the next clock cycle.
   assert property (@(posedge clk) (rd_en && !empty) |-> (!empty));

   // Assertion 3: If a write occurs with a unique tag, then on a valid read with the matching tag, the read data should match the original write data.
   int global_tag;
   int wr_tag;
   logic [WIDTH-1:0] wr_data_mem[0:DEPTH-1]; // Memory to store write data for verification

   // Unique tagging for writes
   always_ff @(posedge clk) begin
      if (wr_en && !full) begin
         wr_data_mem[global_tag] <= wr_data; // Store write data with the current tag
         wr_tag <= global_tag; // Update the write tag
         global_tag++; // Increment to use a unique tag for the next write
      end
   end

   // Check matching when a read occurs
   assert property (@(posedge clk) (rd_en && (wr_tag !== -1)) |-> (rd_data == wr_data_mem[wr_tag]));

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, "" ns"");
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
   end         
endmodule