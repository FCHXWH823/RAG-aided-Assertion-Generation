module register_sva  #(
    parameter WIDTH=8
    )
   (
    input logic              clk,
    input logic              rst,
    input logic              en,
    input logic [WIDTH-1:0]  in,
    input logic [WIDTH-1:0] out
    );

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);
   // For the enable, we can use the same strategy as the FF example.
   // Verify output when enable is asserted.
   assert property(en |=> out == $past(in,1));

   // Verify output when enable isn't asserted. Only one of these is needed
   // since they are equivalent.
   assert property(!en |=> out == $past(out,1));

endmodule
