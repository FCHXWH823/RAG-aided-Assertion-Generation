analyze -clear
analyze -sv12 ./simple_pipeline_assertion.sv

elaborate -top simple_pipeline

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
