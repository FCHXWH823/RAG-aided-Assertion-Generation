analyze -clear
analyze -sv12 ./APB_FSM_Controller_RAG-Openai-4o-mini.sv

elaborate -top APB_FSM_Controller

clock Hclk
reset -expression ~Hresetn
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit
