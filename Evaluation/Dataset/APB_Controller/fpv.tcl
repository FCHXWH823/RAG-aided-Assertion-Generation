analyze -clear
analyze -sv ./APB_Controller.sv
analyze -sv ./APB_Controller_sva.sv
analyze -sv ./APB_Controller_bind.svh

elaborate -top APB_FSM_Controller

clock Hclk
reset -expression ~Hresetn
prove -all
report -summary -force -result -file fpv.rpt
exit
