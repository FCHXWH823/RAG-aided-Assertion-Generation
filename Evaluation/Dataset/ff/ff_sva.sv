module ff_sva(
input logic clk,
input logic rst, 
input logic en,
input logic in,
input logic out
);

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);

   assert property(en |=> out == $past(in,1));

   assert property(!en |=> out == $past(out,1));
   // assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

endmodule

