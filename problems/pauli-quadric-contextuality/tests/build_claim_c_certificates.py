"""Build the 42 submitted elliptic certificate proofs in bounded Lake batches."""
from argparse import ArgumentParser
from datetime import datetime, timezone
from pathlib import Path
import subprocess

def main():
    parser=ArgumentParser()
    parser.add_argument("project",type=Path)
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--batch",type=int,default=2)
    args=parser.parse_args()
    if not 1<=args.batch<=42:parser.error("batch must be between 1 and 42")
    if not (args.project/"lakefile.toml").is_file():parser.error("Lean project missing")
    names=[f"Quadric.Five.Resources.Cert{i:02d}" for i in range(42)]
    for offset in range(0,len(names),args.batch):
        command=[args.lake,"build",*names[offset:offset+args.batch]]
        print(datetime.now(timezone.utc).isoformat(),*command,flush=True)
        result=subprocess.run(command,cwd=args.project)
        print(datetime.now(timezone.utc).isoformat(),f"exit={result.returncode}",flush=True)
        if result.returncode:return result.returncode
    return 0

if __name__=="__main__":raise SystemExit(main())
