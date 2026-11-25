"""Independent regression, witness, hash and rejection testing. Run from this directory."""
from collections import Counter
from hashlib import sha256
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import argparse
import random
import re
import subprocess
import tempfile
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from oracle import exact_full, gaps, verify_certificate

def require(condition, detail):
    if not condition:
        raise ValueError(detail)

def run(p, H):
    """Copy-and-shift implementation. Keep each pass charge by inserted rank."""
    a = list(p)
    trace = []
    for h in H:
        charges = [0]*len(a)
        for i in range(h, len(a)):
            x, j = a[i], i
            while j >= h:
                charges[x] += 1
                if x > a[j-h]:
                    break
                a[j] = a[j-h]
                j -= h
            a[j] = x
        trace.append(charges)
    return a, trace

def edge(n, H, S, x):
    # Literal set operations independent of packed words or mixed-radix indices.
    out = []
    for h in H:
        before = set(range(x%h, x, h))
        s = len(before & S)
        out.append(len(before) - s + int(s != 0))
        T = set()
        for r in range(h):
            chain = list(range(r, n, h))
            T.update(chain[:len(S.intersection(chain))])
        x = x%h + h*sum(i%h == x%h for i in S)
        S = T
    return out

def distribution(n, H):
    full = (1 << n)-1
    counts = [Counter() for _ in range(1 << n)]
    counts[0][0] = 1
    mean_numerator = 0
    for m in range(full):
        S = {i for i in range(n) if m >> i & 1}
        k = len(S)
        for x in set(range(n)) - S:
            value = sum(edge(n, H, S, x))
            mean_numerator += value*factorial(k)*factorial(n-1-k)
            for c, ways in counts[m].items():
                counts[m | (1 << x)][c+value] += ways
    result = counts[full]
    require(sum(c*b for c,b in result.items()) == mean_numerator, ("mean", n, H))
    return result

def I(n, h):
    q,r = divmod(n,h)
    return h*comb(q,2)+r*q

def B(n, h):
    q,r = divmod(n,h)
    return comb(h,2)*comb(q+1,2)+(q+1)*comb(r,2)+n-(r or h)

def nested(n, H):
    value = I(n,H[0])
    for a,b in zip(H,H[1:]):
        m,r = divmod(n,b)
        value += (b-r)*B(m,a//b) + r*B(m+1,a//b)
    return value

def exhaustive(max_n):
    for n in range(2,max_n+1):
        executions = 0
        for m in range(1 << (n-2)):
            H = gaps(n,m)
            poly = distribution(n,H)
            brute = Counter()
            for p in permutations(range(n)):
                a, charges = run(p,H)
                brute[sum(map(sum,charges))] += 1
                executions += 1
            require(poly == brute, ("histogram",n,H))
            require(max(poly) == exact_full(n,H),("DP",n,H))
            if all(a%b==0 for a,b in zip(H,H[1:])):
                require(max(poly)==nested(n,H),("nested",n,H))
        print(f"n={n}: {1 << (n-2)} complete distributions, {executions} executions, nested maxima pass",flush=True)
    rng = random.Random(20261125)
    for _ in range(600):
        n = rng.randint(2,32)
        H = gaps(n,rng.randrange(1 << (n-2)))
        p = rng.sample(range(n),n)
        a, charges = run(p,H)
        require(a==list(range(n)), "final ordering")
        S = set()
        for k in range(n):
            x = p.index(k)
            require(edge(n,H,S,x) == [row[k] for row in charges],("marked charge",n,H,k))
            S.add(x)
    print("600 seeded adversarial rank-by-rank and pass-by-pass comparisons passed")

def hashes_and_winners(binary=None):
    for line in Path("certificate_sha256.txt").read_text().splitlines():
        digest, name = line.split()
        actual = sha256(Path(name).read_bytes()).hexdigest()
        require(actual == digest,name)
        print(name, actual)
    for line in Path("winner_witnesses.txt").read_text().splitlines():
        match = re.fullmatch(r"n=(\d+) gaps=([\d,]+) max=(\d+) witness=([\d,]+)",line)
        n,H,U,p = match.groups()
        n,U=int(n),int(U)
        H,p=([int(x) for x in s.split(",")] for s in [H,p])
        require(sorted(p)==list(range(n)),p)
        a, charges = run(p,H)
        require(a == list(range(n)) and sum(map(sum, charges)) == U,(n,H,p))
        if binary:
            output = subprocess.check_output([binary,str(n),"exact",*map(str,H)],text=True)
            require(f" max={U} " in output,output)
        print(f"witness n={n} gaps={H} pass costs={list(map(sum,charges))} total={U}")
    if binary:
        print("All six mixed-radix maxima matched independent full-subset maxima and literal witnesses.")

def malformed():
    valid = "N 3 3\nO 0\nP 0 2 0 1\nX 1 0\nEND 2\n"
    # For schedule (2,1), a different permutation attains four comparisons.
    p = next(p for p in permutations(range(3)) if sum(map(sum,run(p,[2,1])[1]))==4)
    valid = valid.replace("2 0 1"," ".join(map(str,p)))
    mutations = [
        valid.replace("O 0","B 0"),valid.replace("X 1 0","X 1 1"),
        valid.replace("X 1 0","B 1"),  # baseline equals U
        valid.replace("P 0 "+" ".join(map(str,p)),"P 0 0 1 2"),  # witness cost equals U
        valid.replace("X 1 0","X 1 0 extra"),valid.replace("END 2","END 2 extra"),
        valid.replace("O 0","O 1"),valid.replace("X 1 0","O 1"),
        valid.replace("O 0","O 0 extra"),valid.replace("END 2",""),
        valid.replace("END 2","END 1"),valid+"B 2\n",
        valid.replace("N 3 3","N 3 4"),valid.replace("P 0 "+" ".join(map(str,p)),"P 0 0 0 1"),
        valid.replace("X 1 0","P 0 0 1 2\nX 1 0"),valid.replace("O 0\n",""),
    ]
    with tempfile.TemporaryDirectory() as td:
        path=Path(td)/"cert.txt"
        path.write_text(valid)
        verify_certificate(path)
        for i,bad in enumerate(mutations):
            path.write_text(bad)
            try:
                verify_certificate(path)
            except ValueError:
                continue
            raise ValueError(f"accepted mutation {i}")
    print(f"rejected all {len(mutations)} invalid certificates")

if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--small",type=int,default=7)
    ap.add_argument("--binary")
    args=ap.parse_args()
    hashes_and_winners(args.binary)
    malformed()
    exhaustive(args.small)
