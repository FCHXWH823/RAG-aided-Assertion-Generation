analyze -clear
analyze -sv12 ./arbiter_Dynamic-RAG-Openai-4o-mini.sv

elaborate -top arbiter

clock clk
reset -expression ~rst_n
prove -all
report -summary -force -result -file fpv_Dynamic-RAG-Openai-4o-mini.rpt
exit

