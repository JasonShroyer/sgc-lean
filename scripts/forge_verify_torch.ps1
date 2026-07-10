$conda = "$env:USERPROFILE\miniconda3\Scripts\conda.exe"
& $conda run -n sgc python -c "import torch; print('TORCH', torch.__version__, '| CUDA', torch.version.cuda, '| AVAIL', torch.cuda.is_available(), '| DEV', torch.cuda.get_device_name(0) if torch.cuda.is_available() else 'none')" 2>&1
& $conda run -n sgc python -c "import numpy, scipy, pandas; print('SCI STACK OK', numpy.__version__, scipy.__version__, pandas.__version__)" 2>&1
"=== TFLOPS TEST ==="
& $conda run -n sgc python -c "import torch, time; x=torch.randn(8192,8192,device='cuda'); torch.cuda.synchronize(); t=time.time(); [x@x for _ in range(10)]; torch.cuda.synchronize(); print(f'{10*2*8192**3/(time.time()-t)/1e12:.1f} TFLOPS fp32')" 2>&1
"=== DONE ==="
