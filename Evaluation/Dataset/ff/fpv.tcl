analyze -clear
analyze -sv ./ff.sv
analyze -sv ./ff_sva.sv
analyze -sv ./ff_bind.svh

elaborate -top ff

clock clk
reset -expression rst
prove -all
report -summary -force -result -file ff.fpv.rpt
