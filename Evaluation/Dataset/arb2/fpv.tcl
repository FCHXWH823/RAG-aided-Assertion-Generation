analyze -clear
analyze -sv12 ./arb2.sv
analyze -sv12 ./arb2_sva.sv
analyze -sv12 ./arb2_bind.svh

elaborate -top arb2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

