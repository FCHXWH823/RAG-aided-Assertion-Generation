analyze -clear
analyze -sv12 ./or1200_operandmuxes_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv
analyze -sv12 ./or1200_defines.v

elaborate -top or1200_operandmuxes

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

