analyze -clear
analyze -sv12 ./SEVEN.sv
analyze -sv12 ./SEVEN_sva.sv
analyze -sv12 ./SEVEN_bind.svh

elaborate -top SEVEN

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

