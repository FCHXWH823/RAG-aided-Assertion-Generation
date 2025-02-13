analyze -clear
analyze -sv12 ./host_interface_RAG-Openai-4o-mini.sv

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

