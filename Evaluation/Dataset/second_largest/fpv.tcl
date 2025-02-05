analyze -clear
analyze -sv ./second_largest.sv
analyze -sv ./second_largest_sva.sv
analyze -sv ./second_largest_bind.svh

elaborate -top second_largest

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

