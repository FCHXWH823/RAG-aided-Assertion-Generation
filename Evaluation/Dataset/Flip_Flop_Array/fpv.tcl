analyze -clear
analyze -sv ./Flip_Flop_Array_assertion.sv

elaborate -top Flip_Flop_Array

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

