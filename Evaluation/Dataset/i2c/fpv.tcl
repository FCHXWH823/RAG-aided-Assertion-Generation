analyze -clear
analyze -sv12 ./i2c.sv
analyze -sv12 ./i2c_sva.sv
analyze -sv12 ./i2c_bind.svh

elaborate -top i2c

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

