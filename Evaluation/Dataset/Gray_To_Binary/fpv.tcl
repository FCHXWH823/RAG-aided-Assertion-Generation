analyze -clear
analyze -sv12 ./Gray_To_Binary_assertion.sv

elaborate -top Gray_To_Binary

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv.rpt
exit

