analyze -clear
analyze -sv12 ./host_interface.sv
analyze -sv12 ./host_interface_sva.sv
analyze -sv12 ./host_interface_bind.svh

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

