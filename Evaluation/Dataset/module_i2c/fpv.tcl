analyze -clear
analyze -sv12 ./module_i2c.sv
analyze -sv12 ./module_i2c_sva.sv
analyze -sv12 ./module_i2c_bind.svh

elaborate -top module_i2c

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

