analyze -clear
analyze -sv12 ./create_folder.sh.sv
analyze -sv12 ./create_folder.sh_sva.sv
analyze -sv12 ./create_folder.sh_bind.svh

elaborate -top create_folder.sh

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

