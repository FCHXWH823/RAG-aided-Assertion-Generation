analyze -clear
analyze -sv12 ./arb2_assertion.sv

elaborate -top arb2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

