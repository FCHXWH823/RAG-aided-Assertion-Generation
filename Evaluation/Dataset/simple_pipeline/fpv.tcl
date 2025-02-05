analyze -clear
analyze -sv ./simple_pipeline.sv
analyze -sv ./simple_pipeline_sva.sv
analyze -sv ./simple_pipeline_bind.svh

elaborate -top simple_pipeline

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
