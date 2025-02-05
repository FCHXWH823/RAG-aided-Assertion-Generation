analyze -clear
analyze -sv12 ./simple_req_ack.sv
analyze -sv12 ./simple_req_ack_sva.sv
analyze -sv12 ./simple_req_ack_bind.svh

elaborate -top simple_req_ack

clock clk
reset -expression !rst_n
prove -all
report -summary -force -result -file fpv.rpt
exit

