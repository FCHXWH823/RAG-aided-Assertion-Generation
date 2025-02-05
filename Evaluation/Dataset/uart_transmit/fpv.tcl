analyze -clear
analyze -sv12 ./uart_transmit_assertion.sv

elaborate -top uart_transmit

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

