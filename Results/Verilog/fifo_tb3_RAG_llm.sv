module fifo_tb3_RAG_llm;

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
   logic [WIDTH-1:0] wr_tag; // Tag for write operations
   logic [WIDTH-1:0] rd_tag; // Tag for read operations
   integer serving_id;       // Counter to track writes

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
      serving_id = 0; // Initialize serving_id
      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         wr_tag <= serving_id; // Assign current serving id to the write tag
         serving_id++; // Increment serving id for the next write
         @(posedge clk);         
      end

      disable generate_clock;
      $display("Tests Completed.");
   end

   // Assertion 1: Check that there is never a write while the FIFO is full
   assert property (@(posedge clk) 
      (wr_en && full) |=> $fatal("Error: Write operation attempted while FIFO is full.")
   );

   // Assertion 2: Check that there is never a read while the FIFO is empty
   assert property (@(posedge clk) 
      (rd_en && empty) |=> $fatal("Error: Read operation attempted while FIFO is empty.")
   );

   // Assertion 3: Check that on each valid write, the read matches the original write data with the same tag
   logic valid_write; // To check if write is valid
   logic [WIDTH-1:0] written_data;

   always @(posedge clk) begin
      if (wr_en) begin
         written_data <= wr_data; // Store the written data
         valid_write <= 1'b1; // Mark the write as valid
      end else begin
         valid_write <= 1'b0; // Reset valid write if not writing
      end
   end

   assert property (@(posedge clk) 
      (valid_write && rd_en && (rd_tag == wr_tag)) |=> 
      (rd_data == written_data) ##1
   );

endmodule