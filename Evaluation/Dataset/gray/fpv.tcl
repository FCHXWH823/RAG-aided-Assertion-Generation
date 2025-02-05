analyze -clear
analyze -sv12 ./gray.sv
analyze -sv12 ./gray_sva.sv
analyze -sv12 ./gray_bind.svh

elaborate -top gray

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

