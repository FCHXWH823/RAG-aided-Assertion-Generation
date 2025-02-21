analyze -clear
analyze -sv12 ./control_unit_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top control_unit

clock clk
reset -expression rst_n
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

