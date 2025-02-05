analyze -clear
analyze -sv ./busarbiter.sv
analyze -sv ./busarbiter_sva.sv
analyze -sv ./busarbiter_bind.svh

elaborate -top busarbiter

clock clk
reset -expression reset
prove -all
report -summary -force -result -file fpv.rpt
exit
