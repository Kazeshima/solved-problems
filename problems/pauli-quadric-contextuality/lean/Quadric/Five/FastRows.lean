import Quadric.Five.Gram

namespace Quadric.Five.Certificates
open Small

private def outsideTable : List ℕ :=
  [50,51,54,55,58,59,62,63,84,85,86,87,92,93,94,95,114,115,116,117,122,123,124,125,
   152,153,154,155,156,157,158,159,178,179,182,183,184,185,188,189,212,213,214,215,
   216,217,218,219,242,243,244,245,248,249,254,255]
private theorem outside_eq : outside=outsideTable := by decide +kernel

def fastGraph (sig i j : ℕ) : ℤ :=
  let u:=outsideTable[i]?.getD 0
  let v:=outsideTable[j]?.getD 0
  if i=j ∨ sym 4 u v≠0 then 0 else Small.sign (negative 4 u v ^^ sig.testBit (drop (u^^^v)))

theorem fastGraph_eq (sig i j : ℕ) : fastGraph sig i j=graph sig i j := by
  unfold graph fastGraph; rw [outside_eq]

def rowCuts (ts : List Triangle) (i : ℕ) := ts.filter fun t=> t.a==i || t.b==i

theorem credit_sum (ts : List Triangle) (i j : ℕ) :
    total (rowCuts ts i) (fun t=>credit t (i,j))=total ts (fun t=>credit t (i,j)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold rowCuts at *
    rw [List.filter_cons]
    by_cases h : t.a=i ∨ t.b=i
    · have b : (t.a==i || t.b==i)=true := by simpa using h
      rw [b]; simp only [if_true,total_cons,ih]
    · obtain ⟨ha,hb⟩ := not_or.mp h
      have z : credit t (i,j)=0 := by simp [credit,Ne.symm ha,Ne.symm hb]
      have b : (t.a==i || t.b==i)=false := by simp [ha,hb]
      rw [b]; simp [z,ih]

def quickOff (C : Cert) (ts : List Triangle) (i j : ℕ) :=
  (total ts (fun t=>credit t (i,j))-2*(C.den:ℤ))*fastGraph C.sigma i j

def quickRow (C : Cert) (F : Factor) (i : ℕ) (m : ℤ) : Bool :=
  let ts := rowCuts C.tri i
  (atRow F.rows i).length==56 && m < entry F.residue i i &&
    vertices.all fun j=>i>j || ((F.scale:ℤ)*(if i=j then diagonal C i else quickOff C ts i j) ==
        dotRow F i j+entry F.residue i j)

theorem quickRow_eq (C : Cert) (F : Factor) (i : ℕ) :
    quickRow C F i (errWeight F)=rowValid C F i := by
  simp only [quickRow,quickOff,credit_sum,fastGraph_eq,rowValid,cellOK,off]

def quickTri (sig : ℕ) (t : Triangle) :=
  decide (0≤t.u ∧ t.a<t.b ∧ t.b<t.c ∧ t.c<56 ∧
    fastGraph sig t.a t.b*fastGraph sig t.a t.c*fastGraph sig t.b t.c = -1)

private theorem graph_cases (s i j : ℕ) : graph s i j=0 ∨ graph s i j=1 ∨ graph s i j= -1 := by
  unfold graph; dsimp only; split_ifs <;> simp_all [Small.sign] <;> split <;> tauto

private theorem spin_bound (p q r : ℤ) (hp : p=0 ∨ p=1 ∨ p= -1)
    (hq : q=0 ∨ q=1 ∨ q= -1) (hr : r=0 ∨ r=1 ∨ r= -1) (prod : p*q*r= -1) (a b c : Bool) :
    p*sign a*sign b+q*sign a*sign c+r*sign b*sign c ≤ 1 := by
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> rcases hr with rfl|rfl|rfl <;>
    norm_num at prod <;> cases a <;> cases b <;> cases c <;> decide

theorem quickTri_iff (sig : ℕ) (t : Triangle) :
    quickTri sig t=true ↔ validTri sig t := by
  simp only [quickTri,decide_eq_true_eq,fastGraph_eq,validTri]
  constructor
  · rintro ⟨u,ab,bc,lt,p⟩
    exact ⟨u,ab,bc,lt,p,spin_bound _ _ _ (graph_cases ..) (graph_cases ..) (graph_cases ..) p⟩
  · rintro ⟨u,ab,bc,lt,p,_⟩; exact ⟨u,ab,bc,lt,p⟩

def checksWithoutTriangles (C : Cert) : Bool :=
  decide (0<C.den ∧ C.y.length=56 ∧ 0<C.boundDen ∧
    numerator C*C.boundDen=C.boundNum*C.den ∧
    4*(C.den:ℤ)*(378-(C.floor:ℤ)) ≤ numerator C ∧
    numerator C < 4*(C.den:ℤ)*(379-(C.floor:ℤ)) ∧
    315≤C.count+C.floor ∧ C.count=errors full3 C.sigma.testBit)

theorem checkNumbers_of_parts (C : Cert) (h : checksWithoutTriangles C=true)
    (t : C.tri.all (quickTri C.sigma)=true) : checkNumbers C=true := by
  exact Bool.and_eq_true_iff.mpr ⟨h,List.all_eq_true.mpr (fun x hx=>
    decide_eq_true ((quickTri_iff ..).mp (List.all_eq_true.mp t x hx)))⟩

end Quadric.Five.Certificates
