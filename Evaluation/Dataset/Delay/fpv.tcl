analyze -clear
analyze -sv12 ./Delay.sv
analyze -sv12 ./Delay_sva.sv
analyze -sv12 ./Delay_bind.svh

elaborate -top Delay

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

