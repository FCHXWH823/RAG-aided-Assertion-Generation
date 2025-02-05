analyze -clear
analyze -sv ./Flip-Flop_Array.sv
analyze -sv ./Flip-Flop_Array_sva.sv
analyze -sv ./Flip-Flop_Array_bind.svh

elaborate -top Flip_Flop_Array

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

