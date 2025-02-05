analyze -clear
analyze -sv12 ./host_interface_assertion.sv

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

