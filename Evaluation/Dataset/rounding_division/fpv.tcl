analyze -clear
analyze -sv12 ./rounding_division.sv
analyze -sv12 ./rounding_division_sva.sv
analyze -sv12 ./rounding_division_bind.svh

elaborate -top rounding_division -bbox_m rounding_division_sva

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

