analyze -clear
analyze -sv12 ./host_interface_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

