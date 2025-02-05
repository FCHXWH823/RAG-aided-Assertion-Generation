analyze -clear
analyze -sv12 ./AR.sv
analyze -sv12 ./AR_sva.sv
analyze -sv12 ./AR_bind.svh

elaborate -top AR

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

