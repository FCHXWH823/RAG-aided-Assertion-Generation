analyze -clear
analyze -sv12 ./Edge_Detector_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top Edge_Detector

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

