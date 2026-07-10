Start-Transcript -Path C:\forge\runs\phase2.log -Force
$conda = "$env:USERPROFILE\miniconda3\Scripts\conda.exe"
& $conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/main
& $conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/r
& $conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/msys2
& $conda create -n sgc python=3.12 -y
& $conda run -n sgc python -m pip install torch==2.10.0 torchvision==0.25.0 torchaudio==2.10.0 --index-url https://download.pytorch.org/whl/cu128
& $conda run -n sgc python -m pip install numpy==1.26.4 scipy==1.13.1 pandas==2.2.3 matplotlib==3.11.0 networkx==3.4.2 sympy==1.14.0 tqdm PyYAML
"=== VERIFY ==="
& $conda run -n sgc python -c "import torch; print('TORCH', torch.__version__, '| CUDA', torch.version.cuda, '| AVAIL', torch.cuda.is_available(), '| DEV', torch.cuda.get_device_name(0) if torch.cuda.is_available() else 'none')"
"=== PHASE2 COMPLETE ==="
Stop-Transcript
