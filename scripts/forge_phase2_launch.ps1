schtasks /create /tn sgc_phase2 /tr "powershell -ExecutionPolicy Bypass -File C:\forge\tools\phase2.ps1" /sc once /st 23:59 /f
schtasks /run /tn sgc_phase2
Start-Sleep -Seconds 3
schtasks /query /tn sgc_phase2
