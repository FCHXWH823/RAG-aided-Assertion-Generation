module fifo_tb3;

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

   // Tags for write operations
   logic [WIDTH-1:0] wr_tag;
   logic [WIDTH-1:0] current_tag;
   int global_tag_counter;

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
      global_tag_counter = 0; // Initialize the global tag counter
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;

         // Assign a unique tag for each write operation
         if (wr_en) begin
            wr_tag = global_tag_counter;
            global_tag_counter++;
         end

         @(posedge clk);         
      end

      disable generate_clock;
      $display("Tests Completed.");
   end   

   // Assertion 1: Verify that if a write operation is initiated, then FIFO should not be full in the subsequent clock cycle
   assert property (@(posedge clk) (DUT.valid_wr -> !full));

   // Assertion 2: Verify that if a read operation is initiated, then FIFO should not be empty in the subsequent clock cycle
   assert property (@(posedge clk) (DUT.valid_rd -> !empty));

   // Assertion 3: Check for matching write and read tags
   logic [WIDTH-1:0] saved_write_data;
   logic first_match_found;

   // Function to check for the first matching tag
   function first_match;
      input logic [WIDTH-1:0] tag;
      begin
         // Check if the tag matches the current serving ID
         return (tag == current_tag);
      end
   endfunction

   // Process to handle the write and read operations with matching tags
   always @(posedge clk) begin
      if (wr_en) begin
         saved_write_data <= wr_data; // Save the write data
         current_tag <= wr_tag; // Update the current serving tag
      end

      if (rd_en) begin
         if (first_match(current_tag)) begin
            // Check that read data matches the originally written data on the next cycle
            assert property (@(posedge clk) (DUT.valid_rd && (rd_data == saved_write_data)));
         end
      end
   end

endmodule