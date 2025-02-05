analyze -clear
analyze -sv12 ./thermocouple.sv
analyze -sv12 ./thermocouple_sva.sv
analyze -sv12 ./thermocouple_bind.svh

elaborate -top thermocouple

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

