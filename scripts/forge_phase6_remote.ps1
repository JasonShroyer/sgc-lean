Start-Transcript -Path C:\forge\runs\phase6_anneal.log -Force
$conda = "$env:USERPROFILE\miniconda3\Scripts\conda.exe"
$out = "C:\forge\runs\2026-07-09-charge-anneal\v3"
New-Item -ItemType Directory -Force -Path $out | Out-Null
Copy-Item C:\forge\experiments\charge_anneal_v1.py $out\ -Force
"=== GPU BEFORE ==="
nvidia-smi --query-gpu=name,utilization.gpu,memory.used,temperature.gpu --format=csv,noheader
"=== RUN (n=8, 4 deltas x 1024 seeds, 30k steps, cosine lr, fp64) ==="
& $conda run --no-capture-output -n sgc python C:\forge\experiments\charge_anneal_v1.py --n 8 --seeds 1024 --steps 30000 --log-every 1500 --out $out 2>&1
"RUN EXIT: $LASTEXITCODE"
"=== GPU AFTER ==="
nvidia-smi --query-gpu=name,utilization.gpu,memory.used,temperature.gpu --format=csv,noheader
"=== PHASE6 COMPLETE ==="
Stop-Transcript
