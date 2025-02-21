analyze -clear
analyze -sv12 ./i2c_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top i2c

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

