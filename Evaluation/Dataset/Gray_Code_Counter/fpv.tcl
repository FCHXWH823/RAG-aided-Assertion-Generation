analyze -clear
analyze -sv ./Gray_Code_Counter.sv
analyze -sv ./Gray_Code_Counter_sva.sv
analyze -sv ./Gray_Code_Counter_bind.svh

elaborate -top Gray_Code_Counter

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

