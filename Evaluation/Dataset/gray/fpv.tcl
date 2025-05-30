analyze -clear
analyze -sv12 ./gray_assertion.sv

elaborate -top gray

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

