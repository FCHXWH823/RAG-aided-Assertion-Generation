analyze -clear
analyze -sv ./counter.sv
analyze -sv ./counter_sva.sv
analyze -sv ./counter_bind.svh

elaborate -top counter

clock i_clk
reset -expression i_start_signal
prove -all
report -summary -force -result -file fpv.rpt
exit

