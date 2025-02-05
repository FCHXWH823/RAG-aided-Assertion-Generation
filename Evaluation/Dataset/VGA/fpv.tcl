analyze -clear
analyze -sv12 ./VGA_assertion.sv

elaborate -top VGA

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

