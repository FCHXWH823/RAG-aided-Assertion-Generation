analyze -clear
analyze -sv12 ./fpu_add.sv
analyze -sv12 ./fpu_add_sva.sv
analyze -sv12 ./fpu_add_bind.svh

elaborate -top fpu_add

clock clk
reset rst
prove -all
report -summary -force -result -file fpv.rpt
exit

