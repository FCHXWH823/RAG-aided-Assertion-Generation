analyze -clear
analyze -sv12 ./bitRam.sv
analyze -sv12 ./bitRam_sva.sv
analyze -sv12 ./bitRam_bind.svh

elaborate -top bitRam

clock clk
reset reset
prove -all
report -summary -force -result -file fpv.rpt
exit

