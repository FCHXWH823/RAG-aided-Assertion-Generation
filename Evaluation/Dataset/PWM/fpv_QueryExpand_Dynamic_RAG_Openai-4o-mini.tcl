analyze -clear
analyze -sv12 ./PWM_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top PWM

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

