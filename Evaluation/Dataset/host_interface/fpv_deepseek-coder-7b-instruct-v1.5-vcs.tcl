analyze -clear
analyze -sv12 ./host_interface_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit

