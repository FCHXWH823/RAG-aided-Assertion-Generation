module fifo_sva  #(
    parameter WIDTH=8,
    parameter DEPTH=16
    )
   (
    input logic              clk,
    input logic              rst,
    input logic             full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    input logic             empty, 
    input logic              rd_en,
    input logic [WIDTH-1:0] rd_data,  
    input logic valid_wr, 
    input logic valid_rd
    );

   default clocking cb @(posedge clk);
   endclocking
   default disable iff (rst);
   assert property (valid_wr |-> !full);
   assert property (valid_rd |-> !empty);

endmodule
