analyze -clear
analyze -sv12 ./simple_pipeline_en.sv
analyze -sv12 ./simple_pipeline_en_sva.sv
analyze -sv12 ./simple_pipeline_en_bind.svh

elaborate -top simple_pipeline_en
clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
