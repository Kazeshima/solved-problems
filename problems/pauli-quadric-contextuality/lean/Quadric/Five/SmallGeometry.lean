import Quadric.Five.Elimination
import Mathlib.Data.Nat.Bitwise

namespace Quadric.Five.Small

def pc : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,x => (x%2)+pc n (x/2)
def xpart (n v : ℕ) := v % (2^n)
def zpart (n v : ℕ) := v / (2^n)
def ys (n v : ℕ) := pc n (xpart n v &&& zpart n v)
def sym (n u v : ℕ) := (pc n (zpart n u &&& xpart n v)+pc n (zpart n v &&& xpart n u))%2
/-- Sign exponent for a commuting product in the tensor-Hermitian representatives Y=iXZ. -/
def negative (n u v : ℕ) : Bool :=
  ((4*n+ys n u+ys n v-ys n (u^^^v)+2*pc n (zpart n u &&& xpart n v))%4)==2

structure Line where
  a : ℕ
  b : ℕ
  c : ℕ
  neg : Bool
  deriving DecidableEq, Repr

def labels (n : ℕ) := (List.range (2^(2*n))).drop 1
def lineList (n : ℕ) (ps : List ℕ) : List Line :=
  ps.flatMap fun a => (ps.filter fun b => a<b && b<(a^^^b) && sym n a b == 0 &&
    ps.contains (a^^^b)).map fun b => ⟨a,b,a^^^b,negative n a b⟩

def full3 := lineList 3 (labels 3)
def failure (s : ℕ → Bool) (l : Line) := s l.a ^^ s l.b ^^ s l.c ^^ l.neg
def errors (ls : List Line) (s : ℕ → Bool) : ℕ := ls.countP (failure s)
def unpack (s : ℕ) (p : ℕ) := s.testBit p

def elliptic (p : ℕ) := (ys 4 p + sym 4 17 p)%2==0
def ellipticPts := (labels 4).filter elliptic
def outside := ellipticPts.filter fun p => sym 4 1 p != 0
def drop (p : ℕ) := (xpart 4 p)/2 + 8*((zpart 4 p)/2)
def sign (b : Bool) : ℤ := if b then -1 else 1

def graph (sig i j : ℕ) : ℤ :=
  let u := outside[i]?.getD 0
  let v := outside[j]?.getD 0
  if i=j ∨ sym 4 u v ≠ 0 then 0
  else sign (negative 4 u v ^^ sig.testBit (drop (u^^^v)))

def pairs {α : Type*} : List α → List (α×α)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ pairs xs

def vertices := List.range 56
def edges := pairs vertices

def isEdge (i j : ℕ) : Bool :=
  i != j && sym 4 (outside[i]?.getD 0) (outside[j]?.getD 0) == 0

theorem graph_eq (sig i j : ℕ) : graph sig i j =
    if isEdge i j then sign (negative 4 (outside[i]?.getD 0) (outside[j]?.getD 0) ^^
      sig.testBit (drop ((outside[i]?.getD 0) ^^^ (outside[j]?.getD 0)))) else 0 := by
  by_cases h : i=j <;> by_cases k : sym 4 (outside[i]?.getD 0) (outside[j]?.getD 0)=0 <;>
    simp [graph,isEdge,h,k]

theorem outside_count : outside.length=56 := by decide +kernel
theorem edge_count : edges.countP (fun ij => isEdge ij.1 ij.2)=756 := by decide +kernel
theorem full3_count : full3.length=315 := by decide +kernel

end Quadric.Five.Small

