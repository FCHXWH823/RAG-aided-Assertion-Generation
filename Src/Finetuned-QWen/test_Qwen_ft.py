from huggingface_hub import snapshot_download

model_id="Jalik/Qwen-2.5-Coder-Instruct-NL2SVA-7B-Prompt"
snapshot_download(repo_id=model_id, local_dir="ft-nl2sva-7b-prompt",
                          local_dir_use_symlinks=False, revision="main")