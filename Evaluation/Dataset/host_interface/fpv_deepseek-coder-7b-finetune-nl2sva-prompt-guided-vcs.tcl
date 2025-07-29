analyze -clear
analyze -sv12 ./host_interface_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top host_interface

clock HCLK
reset -expression !HRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

