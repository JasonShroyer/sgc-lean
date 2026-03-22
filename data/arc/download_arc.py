"""
Download ARC dataset from the official repository.
"""

import urllib.request
import json
import os
from pathlib import Path

ARC_REPO_BASE = "https://raw.githubusercontent.com/fchollet/ARC-AGI/master/data"

# ARC training set task IDs (first 100)
SAMPLE_TASKS = [
    "007bbfb7", "00d62c1b", "017c7c7b", "025d127b", "045e512c",
    "0520fde7", "05269061", "05f2a901", "06df4c85", "08ed6ac7",
    "09629e4f", "0962bcdd", "0a938d79", "0b148d64", "0ca9ddb6",
    "0d3d703e", "0dfd9992", "0e206a2e", "10fcaaa3", "11852cab",
    "1190e5a7", "137eaa46", "150deff5", "1a07d186", "1b2d62fb",
    "1b60fb0c", "1bfc4729", "1c786137", "1caeab9d", "1cf80156",
    "1e0a9b12", "1e32b0e9", "1f0c79e5", "1f642eb9", "1f85a75f",
    "2013d3e2", "2204b7a8", "22168020", "22233c11", "2281f1f4",
    "228f6490", "22eb0ac0", "234bbc79", "23581191", "239be575",
    "23b5c85d", "253bf280", "25d487eb", "25d8a9c8", "25ff71a9",
    "264363fd", "272f95fa", "27a28665", "28bf18c6", "28e73c20",
    "29623171", "29c11459", "29ec7d0e", "2bee17df", "2c608aff",
    "2dc579da", "2dd70a9a", "2dee498d", "31aa019c", "321b1fc6",
    "32597951", "3345333e", "3428a4f5", "3618c87e", "3631a71a",
    "36d67576", "36fdfd69", "3906de3d", "39a8645d", "39e1d7f9",
    "3aa6fb7a", "3ac3eb23", "3af2c5a8", "3bd67248", "3bdb4ada",
    "3befdf3e", "3c9b0459", "3de23699", "3e980e27", "3eda0437",
    "3f7978a0", "40853293", "4093f84a", "41e4d17e", "4258a5f9",
    "42a50994", "4290ef0e", "4347f46a", "444801d8", "44d8ac46",
    "44f52bb0", "4522001f", "456873bc", "45737921", "4612dd53"
]


def download_task(task_id: str, output_dir: Path) -> bool:
    """Download a single ARC task."""
    url = f"{ARC_REPO_BASE}/training/{task_id}.json"
    output_path = output_dir / f"{task_id}.json"
    
    if output_path.exists():
        print(f"  {task_id}: Already exists")
        return True
    
    try:
        print(f"  {task_id}: Downloading...")
        with urllib.request.urlopen(url, timeout=10) as response:
            data = response.read().decode('utf-8')
            
        # Validate JSON
        json.loads(data)
        
        with open(output_path, 'w') as f:
            f.write(data)
        
        print(f"  {task_id}: OK")
        return True
        
    except Exception as e:
        print(f"  {task_id}: FAILED ({e})")
        return False


def create_sample_tasks(output_dir: Path):
    """Create sample ARC-like tasks for testing if download fails."""
    
    # Task 1: Simple rotation
    task1 = {
        "train": [
            {"input": [[1,2,3],[4,5,6],[7,8,9]], "output": [[7,4,1],[8,5,2],[9,6,3]]},
            {"input": [[1,0,0],[0,1,0],[0,0,1]], "output": [[0,0,1],[0,1,0],[1,0,0]]}
        ],
        "test": [
            {"input": [[1,1,2],[3,3,4],[5,5,6]], "output": [[5,3,1],[5,3,1],[6,4,2]]}
        ]
    }
    
    # Task 2: Color swap
    task2 = {
        "train": [
            {"input": [[1,1,1],[2,2,2],[1,1,1]], "output": [[2,2,2],[1,1,1],[2,2,2]]},
            {"input": [[1,2,1],[2,1,2]], "output": [[2,1,2],[1,2,1]]}
        ],
        "test": [
            {"input": [[1,1],[2,2],[1,1]], "output": [[2,2],[1,1],[2,2]]}
        ]
    }
    
    # Task 3: Horizontal flip
    task3 = {
        "train": [
            {"input": [[1,2,3],[4,5,6]], "output": [[3,2,1],[6,5,4]]},
            {"input": [[1,0],[0,2]], "output": [[0,1],[2,0]]}
        ],
        "test": [
            {"input": [[1,2,3,4]], "output": [[4,3,2,1]]}
        ]
    }
    
    # Task 4: Vertical flip  
    task4 = {
        "train": [
            {"input": [[1,2],[3,4],[5,6]], "output": [[5,6],[3,4],[1,2]]},
            {"input": [[1],[2],[3]], "output": [[3],[2],[1]]}
        ],
        "test": [
            {"input": [[1,0],[0,1]], "output": [[0,1],[1,0]]}
        ]
    }
    
    # Task 5: Fill with single color
    task5 = {
        "train": [
            {"input": [[1,2,3],[4,5,6]], "output": [[7,7,7],[7,7,7]]},
            {"input": [[0,1,0],[2,0,3]], "output": [[0,7,0],[7,0,7]]}
        ],
        "test": [
            {"input": [[1,2],[3,4]], "output": [[7,7],[7,7]]}
        ]
    }
    
    # Task 6: Identity (already solved)
    task6 = {
        "train": [
            {"input": [[1,2],[3,4]], "output": [[1,2],[3,4]]},
            {"input": [[5]], "output": [[5]]}
        ],
        "test": [
            {"input": [[1,1,1]], "output": [[1,1,1]]}
        ]
    }
    
    # Task 7: Crop to content
    task7 = {
        "train": [
            {"input": [[0,0,0,0],[0,1,2,0],[0,3,4,0],[0,0,0,0]], "output": [[1,2],[3,4]]},
            {"input": [[0,0,0],[0,5,0],[0,0,0]], "output": [[5]]}
        ],
        "test": [
            {"input": [[0,0,0],[0,1,0],[0,0,0]], "output": [[1]]}
        ]
    }
    
    # Task 8: 2x upscale
    task8 = {
        "train": [
            {"input": [[1,2],[3,4]], "output": [[1,1,2,2],[1,1,2,2],[3,3,4,4],[3,3,4,4]]},
            {"input": [[5]], "output": [[5,5],[5,5]]}
        ],
        "test": [
            {"input": [[1]], "output": [[1,1],[1,1]]}
        ]
    }
    
    # Task 9: Rotate 180
    task9 = {
        "train": [
            {"input": [[1,2],[3,4]], "output": [[4,3],[2,1]]},
            {"input": [[1,0,0],[0,0,0]], "output": [[0,0,0],[0,0,1]]}
        ],
        "test": [
            {"input": [[1,2,3]], "output": [[3,2,1]]}
        ]
    }
    
    # Task 10: Composition (flip + rotate)
    task10 = {
        "train": [
            {"input": [[1,2,3],[0,0,0],[0,0,0]], "output": [[1,0,0],[2,0,0],[3,0,0]]},
            {"input": [[1,0],[2,0],[3,0]], "output": [[1,2,3],[0,0,0]]}
        ],
        "test": [
            {"input": [[1,2],[0,0]], "output": [[1,0],[2,0]]}
        ]
    }
    
    tasks = {
        "sample_rotation": task1,
        "sample_colorswap": task2,
        "sample_fliph": task3,
        "sample_flipv": task4,
        "sample_fill": task5,
        "sample_identity": task6,
        "sample_crop": task7,
        "sample_upscale": task8,
        "sample_rotate180": task9,
        "sample_composition": task10
    }
    
    print("\nCreating sample tasks...")
    for name, task in tasks.items():
        path = output_dir / f"{name}.json"
        with open(path, 'w') as f:
            json.dump(task, f, indent=2)
        print(f"  {name}: Created")


def main():
    output_dir = Path(__file__).parent / "training"
    output_dir.mkdir(exist_ok=True)
    
    print("ARC Data Downloader")
    print("=" * 40)
    print(f"Output: {output_dir}")
    
    # Try to download real ARC tasks
    print("\nDownloading ARC tasks...")
    success_count = 0
    for task_id in SAMPLE_TASKS:
        if download_task(task_id, output_dir):
            success_count += 1
    
    print(f"\nDownloaded: {success_count}/{len(SAMPLE_TASKS)}")
    
    # If download failed, create sample tasks
    if success_count < 5:
        print("\nDownload incomplete. Creating sample tasks instead...")
        create_sample_tasks(output_dir)
    
    # List final contents
    print("\nFinal contents:")
    for f in sorted(output_dir.glob("*.json")):
        print(f"  {f.name}")


if __name__ == "__main__":
    main()
