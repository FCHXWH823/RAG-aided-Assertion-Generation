analyze -clear
analyze -sv12 ./uartTrans_assertion.sv

elaborate -top uartTrans

clock clk
reset reset
prove -all
report -summary -force -result -file fpv.rpt
exit

