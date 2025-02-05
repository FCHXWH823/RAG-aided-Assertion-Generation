analyze -clear
analyze -sv12 ./PSGBusArb_assertion.sv

elaborate -top PSGBusArb

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

