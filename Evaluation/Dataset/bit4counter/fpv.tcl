analyze -clear
analyze -sv12 ./bit4counter.sv
analyze -sv12 ./bit4counter_sva.sv
analyze -sv12 ./bit4counter_bind.svh

elaborate -top bit4counter

clock clk
reset -expression reset
prove -all
report -summary -force -result -file fpv.rpt
exit

