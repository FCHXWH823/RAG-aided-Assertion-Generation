analyze -clear
analyze -sv12 ./APB_FSM_Controller_deepseek-coder-7b-instruct-v1.5-vcs.sv

elaborate -top APB_FSM_Controller

clock Hclk
reset -expression ~Hresetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-instruct-v1.5-vcs.rpt
exit
