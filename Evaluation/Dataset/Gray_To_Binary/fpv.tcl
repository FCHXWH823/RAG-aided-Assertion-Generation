analyze -clear
analyze -sv ./Gray_To_Binary.sv
analyze -sv ./Gray_To_Binary_sva.sv
analyze -sv ./Gray_To_Binary_bind.svh

elaborate -top Gray_To_Binary

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv.rpt
exit

