"""Independent, simple exact DP using all subsets, not C++ mixed-radix code.
Also independently verify per-schedule lower-bound certificates.
"""
import argparse
import itertools
from pathlib import Path

def gaps(n, mask):
    return [h for h in range(n-1, 1, -1) if mask & (1 << (h-2))] + [1]

def literal_cost(a, H):
    a = list(a)
    c = 0
    for h in H:
        for r in range(h):
            for i in range(r+h, len(a), h):
                j = i
                while j >= h:
                    c += 1
                    if a[j-h] < a[j]:
                        break
                    a[j-h], a[j] = a[j], a[j-h]
                    j -= h
    if a != sorted(a):
        raise ValueError('execution did not finish in sorted order')
    return c

def exact_full(n, H):
    if n < 2 or not H or H[-1] != 1 or H[0] >= n or any(a <= b for a,b in zip(H,H[1:])):
        raise ValueError('expected strictly decreasing positive gaps below n ending in 1')
    # For each original subset S, propagate S and the newly added rank.
    # Binary pass output depends only on each residue's small-key count.
    full = (1 << n) - 1
    cm = {h: [sum(1 << i for i in range(r,n,h)) for r in range(h)] for h in H}
    pred = {h: [sum(1 << j for j in range(i%h,i,h)) for i in range(n)] for h in H}
    pack = {h: [[sum(1 << (r+i*h) for i in range(k))
                 for k in range(cm[h][r].bit_count()+1)] for r in range(h)] for h in H}
    dp = [-1] * (full+1)
    dp[0] = 0
    for S in range(full):
        # Precompute each pass input subset and its chain counts.
        A = S
        cache = []
        for h in H:
            counts = [(A & m).bit_count() for m in cm[h]]
            cache.append((h, A, counts))
            A = sum(pack[h][r][k] for r,k in enumerate(counts))
        unused = full ^ S
        while unused:
            bit = unused & -unused
            unused ^= bit
            x = bit.bit_length()-1
            c = dp[S]
            for h,A,counts in cache:
                small = (A & pred[h][x]).bit_count()
                c += x//h-small + (small > 0)
                x = x%h + h*counts[x%h]
            if c > dp[S|bit]: dp[S|bit] = c
    return dp[full]

def verify_certificate(path, check_upper=True, upper_solver=exact_full):
    """Reject incomplete, ambiguous or invalid records even under python -O."""
    pool = {}
    expected = 0
    winners = []
    counts = dict(B=0, X=0, O=0)
    ended = False
    with open(path, encoding="ascii") as stream:
        header = stream.readline().split()
        if len(header) != 3 or header[0] != "N":
            raise ValueError("invalid header")
        n, optimum = map(int, header[1:])
        if n < 2 or optimum < 0:
            raise ValueError("invalid size or optimum")
        total = 1 << (n - 2)
        for line_number, line in enumerate(stream, 2):
            fields = line.split()
            if not fields or ended:
                raise ValueError(f"unexpected line {line_number}")
            tag, *args = fields
            arity = {"P": n+1, "B": 1, "X": 2, "O": 1, "END": 1}.get(tag)
            if len(args) != arity:
                raise ValueError(f"invalid {tag} record at line {line_number}")
            values = list(map(int, args))
            if tag == "P":
                index, *p = values
                if index < 0 or index in pool or sorted(p) != list(range(n)):
                    raise ValueError(f"invalid permutation at line {line_number}")
                pool[index] = p
                continue
            if tag == "END":
                if values[0] != total or expected != total:
                    raise ValueError("incomplete coverage")
                ended = True
                continue
            mask = values[0]
            if mask != expected or mask >= total:
                raise ValueError(f"unexpected mask at line {line_number}")
            expected += 1
            H = gaps(n, mask)
            counts[tag] += 1
            if tag == "B" and sum(n-h for h in H) <= optimum:
                raise ValueError(f"baseline does not strictly reject {mask}")
            if tag == "X":
                witness = pool.get(values[1])
                if witness is None or literal_cost(witness, H) <= optimum:
                    raise ValueError(f"invalid witness exclusion at {mask}")
            if tag == "O":
                if check_upper and upper_solver(n, H) != optimum:
                    raise ValueError(f"wrong exact cost at {mask}")
                winners.append(H)
    if not ended or not winners:
        raise ValueError("missing end or winners")
    status = "complete" if check_upper else "exclusions only"
    print(f"{path}: {status}, n={n}, U={optimum}, masks={expected}, rows={counts}, "
          f"distinct witnesses={len(pool)}, listed winners={winners}", flush=True)
    return n, optimum, winners, counts

def check_small(max_n):
    checked=0; nperms=0
    for n in range(2,max_n+1):
        allp=list(itertools.permutations(range(n)))
        for mask in range(1<<(n-2)):
            H=gaps(n,mask)
            actual=max(literal_cost(p,H) for p in allp)
            dp=exact_full(n,H)
            if actual != dp:
                raise ValueError((n, H, actual, dp))
            checked+=1;nperms+=len(allp)
        print(f'checked n={n}, cumulative schedules={checked}, permutations-times-schedules={nperms}',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--small',type=int); ap.add_argument('--certificate',nargs='*'); ap.add_argument('--skip-upper',action='store_true'); ap.add_argument('--exact',nargs='+',type=int)
    a=ap.parse_args()
    if a.small: check_small(a.small)
    if a.certificate:
        for p in a.certificate: verify_certificate(p,not a.skip_upper)
    if a.exact:
        n,*H=a.exact; print(f'independent exact n={n} gaps={H} max={exact_full(n,H)}',flush=True)
