analyze -clear
analyze -sv12 ./fpu_sub.sv
analyze -sv12 ./fpu_sub_sva.sv
analyze -sv12 ./fpu_sub_bind.svh

elaborate -top fpu_sub

clock clk
reset rst
prove -all
report -summary -force -result -file fpv.rpt
exit

