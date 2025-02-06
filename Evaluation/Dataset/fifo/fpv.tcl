analyze -clear
analyze -sv12 ./fifo_assertion.sv

elaborate -top fifo

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
