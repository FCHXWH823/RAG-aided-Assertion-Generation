analyze -clear
analyze -sv ./fifo.sv
analyze -sv ./fifo_sva.sv
analyze -sv ./fifo_bind.svh

elaborate -top fifo

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
