analyze -clear
analyze -sv12 ./uartRec_assertion.sv

elaborate -top uartRec

clock clk
reset reset
prove -all
report -summary -force -result -file fpv.rpt
exit

