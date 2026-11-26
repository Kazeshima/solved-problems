"""Produce untrusted integer Gram witnesses for Jonah's original matrices.

All entries are rechecked in Lean; floating point only suggests a factor. Use --case for a
single case. Source generation is scoped to the claim-C certificate directory.
"""
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT, OUT, read, matrix, write_record, lmat

def make_factor(rec):
    import numpy as np
    up=matrix(rec); N=len(up)
    M=[[up[min(i,j)][abs(i-j)] for j in range(N)] for i in range(N)]
    A=np.asarray(M,dtype=np.float64)
    minimum=float(np.linalg.eigvalsh(A)[0])
    if minimum<=0: raise ArithmeticError("candidate factor unavailable")
    chol=np.linalg.cholesky(A-0.5*minimum*np.eye(N))
    for bits in (16,20,24,28,32,36,40,44,48):
        k=1<<bits
        L=[[round(float(v)*k) for v in row] for row in chol]
        R=[[M[i][j]*k*k-sum(x*y for x,y in zip(L[i],L[j])) if i<=j else 0
            for j in range(N)] for i in range(N)]
        mass=2*sum(abs(R[i][j]) for i in range(N) for j in range(i+1,N))
        if all(R[i][i]>mass for i in range(N)):
            return k*k,L,R,mass
    raise ArithmeticError("insufficient exact margin")

def compact(m):
    return "intRows% "+json.dumps(";".join(",".join(map(str,row)) for row in m))

def source(rec,hash_value):
    i=rec["id"]; nm=f"{i:02d}"; c="cert"+nm; f="factor"+nm
    scale,L,R,mass=make_factor(rec)
    s="import Quadric.Five.Gram\nimport Quadric.Five.Literals\n\nnamespace Quadric.Five.Certificates.Data\nopen Small\n"
    s+="set_option maxRecDepth 16384\nset_option maxHeartbeats 16000000\nset_option Elab.async false\n\n"
    s+="/- Public L7R integer certificate "+str(i)+". SHA-256 of the full original text: "+hash_value+". -/\n"
    record=write_record(rec).replace("def "+c,"noncomputable def "+c)
    if rec["tri"]:
        old="["+",\n".join("⟨"+",".join(map(str,t))+"⟩" for t in rec["tri"])+"]"
        record=record.replace(old,"("+compact(rec["tri"])+").map (fun r => ⟨(r[0]?.getD 0).toNat,(r[1]?.getD 0).toNat,(r[2]?.getD 0).toNat,r[3]?.getD 0⟩)")
    if rec["tri"]:
        s=s.replace("import Quadric.Five.Gram","import Quadric.Five.TriLiterals")
        a=record.index("("+compact(rec["tri"])+")")
        b=record.index("⟩)",a)+2
        record=record[:a]+"triangleRows% "+json.dumps(";".join(",".join(map(str,t)) for t in rec["tri"]))+record[b:]
    s+=record
    s+=f"\nprivate noncomputable def {f} : Factor := ⟨{scale},\n"+compact(L)+",\n"+compact(R)+"⟩\n"
    s+=f"private theorem mass{nm} : errWeight {f} = {mass} := by decide +kernel\n"
    if rec["tri"]:
        s+=f"private theorem numbers{nm} : checkNumbers {c} = true :=\n  checkNumbers_of_parts {c} (by decide +kernel) (by decide +kernel)\n"
    else:
        s+=f"private theorem numbers{nm} : checkNumbers {c} = true := by decide +kernel\n"
    for row in range(56):
        s+=f"private theorem row{nm}_{row} : rowValid {c} {f} {row} = true := by\n"
        if rec["tri"]:
            s+=f"  rw [←quickRow_eq,mass{nm}]; decide +kernel\n"
        else:
            s+=f"  unfold rowValid; rw [mass{nm}]; decide +kernel\n"
    s+=f"private theorem rows{nm} : RowSpan {c} {f} 0 56 :=\n  ⟨"+", ".join(f"row{nm}_{j}" for j in range(56))+", trivial⟩\n"
    s+=f"theorem bound{nm} (s : ℕ → Bool) : 315 ≤ errors full3 {c}.sigma.testBit + outsideErrors {c}.sigma s :=\n"
    s+=f"  certificate_bound {c} numbers{nm} s (gram_positive {c} {f} (by decide +kernel)\n"
    s+=f"    (rows_valid {c} {f} rows{nm}) (fun i => sign (s i)))\n"
    s+="end Quadric.Five.Certificates.Data\n"
    return s
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',type=int,action='append')
    args=ap.parse_args();cs,digest=read(); OUT.mkdir(parents=True,exist_ok=True)
    for j in (args.case if args.case else range(42)):
        text=source(cs[j],digest)
        (OUT/('Cert%02d.lean'%j)).write_text(text,encoding='utf8')
        print(j,len(text),flush=True)
