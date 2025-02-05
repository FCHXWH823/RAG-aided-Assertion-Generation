analyze -clear
analyze -sv ./APB_FSM_Controller_assertion.sv

elaborate -top APB_FSM_Controller

clock Hclk
reset -expression ~Hresetn
prove -all
report -summary -force -result -file fpv.rpt
exit
