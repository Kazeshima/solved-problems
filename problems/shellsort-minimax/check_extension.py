"""Replay every exclusion, calculate every full-lattice upper bound, replay every winning witness."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from oracle import verify_certificate, literal_cost

def check(path, full_solver, mixed_solver):
    print(path, sha256(Path(path).read_bytes()).hexdigest(),flush=True)
    def upper(n, H):
        args = [str(n),*map(str,H)]
        out = subprocess.check_output([full_solver,*args],text=True).strip()
        print(out,flush=True)
        m = re.fullmatch(r"n=(\d+) gaps=([\d,]+) states=(\d+) edges=(\d+) max=(\d+)",out)
        if m is None or (int(m[1]),m[2],int(m[3]),int(m[4])) != (n,",".join(map(str,H))+",",1<<n,n*(1<<(n-1))):
            raise ValueError("invalid full-lattice solver result")
        value=int(m[5])
        out=subprocess.check_output([mixed_solver,str(n),"exact",*map(str,H)],text=True).strip()
        print(out,flush=True)
        witness_match=re.fullmatch(r"n=(\d+) gaps=([\d,]+) max=(\d+) witness=([\d,]+)",out)
        if witness_match is None: raise ValueError("invalid mixed-radix output")
        p=list(map(int,witness_match[4].split(",")))
        if (sorted(p) != list(range(n)) or int(witness_match[1])!=n or witness_match[2]!=",".join(map(str,H))
                or int(witness_match[3])!=value or literal_cost(p,H)!=value):
            raise ValueError("wrong maximizing witness")
        return value
    verify_certificate(path,upper_solver=upper)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("certificates",nargs="+")
    ap.add_argument("--full",required=True)
    ap.add_argument("--mixed",required=True)
    args=ap.parse_args()
    for path in args.certificates: check(path,args.full,args.mixed)
