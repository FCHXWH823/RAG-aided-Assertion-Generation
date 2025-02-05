analyze -clear
analyze -sv12 ./three_processor_bin_2.sv
analyze -sv12 ./three_processor_bin_2_sva.sv
analyze -sv12 ./three_processor_bin_2_bind.svh

elaborate -top three_processor_bin_2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

