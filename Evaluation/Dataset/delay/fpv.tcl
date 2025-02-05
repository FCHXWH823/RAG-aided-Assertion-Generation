analyze -clear
analyze -sv ./delay.sv
#analyze -sv ./delay_sva.sv
#analyze -sv ./delay_bind.svh

elaborate -top delay

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

