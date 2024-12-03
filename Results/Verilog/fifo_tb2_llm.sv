"Here is a rewritten version of the provided Verilog code with the requested assertions added. The assertions ensure the FIFO properties regarding full/empty conditions and validate the read/write operations as specified.

```verilog
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

   // Assertion 1: Check that there is never a write when FIFO is full
   assert property (@(posedge clk) (wr_en && full) |-> 0) 
      else $error(""Write attempted to full FIFO at time %t"", $time);

   // Assertion 2: Check that there is never a read when FIFO is empty
   assert property (@(posedge clk) (rd_en && empty) |-> 0) 
      else $error(""Read attempted from empty FIFO at time %t"", $time);

   // Assertion 3: Ensuring valid write leads to valid read with matching data
   logic [WIDTH-1:0] data;
   property valid_write_to_read;
      @(posedge clk) 
      (wr_en && !full) |-> 
      (data = wr_data) ##[1:$] (rd_en && !empty && (rd_data == data));
   endproperty

   assert property (valid_write_to_read) 
   @(posedge clk) (wr_en && !full) |-> 
      ##[1:$] (rd_en && !empty && (rd_data == data)) 
      else $display(""Matching read data at time %t: %0h"", $time, rd_data);
   
endmodule
```

### Explanation of Assertions:

1. **Assertion 1**: Ensures that when a write enable (`wr_en`) signal is high and the FIFO is full, the condition is false. If it ever becomes true, an error message is printed with the current simulation time.

2. **Assertion 2**: Similar to Assertion 1 but for the read operation. It checks that when the read enable (`rd_en`) signal is high and the FIFO is empty, the condition is false, and if it becomes true, it prints an error message.

3. **Assertion 3**: It first saves the `wr_data` to a local variable `data` when there is a valid write. The property then asserts that at some point in the future, if a read operation (`rd_en`) is performed while the FIFO is not empty, the read data (`rd_data`) should match the previously written data. If this condition fails, a message is printed along with the mismatched read data."
