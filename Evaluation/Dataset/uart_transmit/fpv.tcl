analyze -clear
analyze -sv12 ./uart_transmit.sv
analyze -sv12 ./uart_transmit_sva.sv
analyze -sv12 ./uart_transmit_bind.svh

elaborate -top uart_transmit

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

