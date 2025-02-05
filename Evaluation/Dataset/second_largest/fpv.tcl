analyze -clear
analyze -sv ./second_largest_assertion.sv

elaborate -top second_largest

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

