"""Download ARC evaluation set (400 tasks) from GitHub."""
import urllib.request
import json
import os
from pathlib import Path
import time

ARC_REPO_BASE = "https://raw.githubusercontent.com/fchollet/ARC-AGI/master/data"

def main():
    eval_dir = Path(__file__).parent / "evaluation"
    eval_dir.mkdir(exist_ok=True)
    
    existing = list(eval_dir.glob("*.json"))
    print(f"Existing: {len(existing)} files")
    
    # Get task list from GitHub API
    url = "https://api.github.com/repos/fchollet/ARC-AGI/contents/data/evaluation"
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    resp = urllib.request.urlopen(req, timeout=15)
    data = json.loads(resp.read())
    task_ids = [f["name"].replace(".json", "") for f in data if f["name"].endswith(".json")]
    print(f"Found {len(task_ids)} evaluation tasks")
    
    success = 0
    skip = 0
    fail = 0
    for i, tid in enumerate(task_ids):
        out_path = eval_dir / f"{tid}.json"
        if out_path.exists():
            skip += 1
            continue
        
        task_url = f"{ARC_REPO_BASE}/evaluation/{tid}.json"
        try:
            req = urllib.request.Request(task_url, headers={"User-Agent": "Mozilla/5.0"})
            resp = urllib.request.urlopen(req, timeout=10)
            content = resp.read().decode("utf-8")
            json.loads(content)  # validate
            with open(out_path, "w") as f:
                f.write(content)
            success += 1
            if (success + skip) % 50 == 0:
                print(f"  Progress: {success + skip}/{len(task_ids)} downloaded")
        except Exception as e:
            fail += 1
            print(f"  FAIL {tid}: {e}")
        
        # Rate limit
        if success % 10 == 0 and success > 0:
            time.sleep(0.5)
    
    print(f"\nDone: {success} downloaded, {skip} skipped, {fail} failed")
    total = len(list(eval_dir.glob("*.json")))
    print(f"Total evaluation files: {total}")

if __name__ == "__main__":
    main()
