analyze -clear
analyze -sv12 ./or1200_operandmuxes.sv
analyze -sv12 ./or1200_defines.v

elaborate -top or1200_operandmuxes

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

