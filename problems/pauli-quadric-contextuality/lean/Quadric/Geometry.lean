import Quadric.Pauli
import Mathlib.Data.List.Sort

/-! The binary representation below uses the low three bits for X and the next three for Z.
Each 2- or 3-space has a unique reverse-pivot reduced row echelon basis. Incidence is membership
of both rows of a 2-space in the binary row span of a 3-space. The target uses four bits per block.
All lists are derived from coordinates. -/
namespace Quadric.Dual
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
open List

abbrev Plane := Nat × Nat
abbrev Frame := Nat × Nat × Nat
def parity3 (x : Nat) := (x ^^^ (x >>> 1) ^^^ (x >>> 2)) % 2
def parity4 (x : Nat) := (parity3 x + (x >>> 3)) % 2
def symp (x y : Nat) := parity3 ((x &&& (y >>> 3)) ^^^ (y &&& (x >>> 3)))
/-- Largest place value of a nonzero six-bit row. -/
def pivot (y : Nat) : Nat :=
  if y < 2 then 1 else if y < 4 then 2 else if y < 8 then 4
    else if y < 16 then 8 else if y < 32 then 16 else 32
def before (x y : Nat) : Bool := y != 0 && (x &&& pivot y) == 0

def planeRow (x : Nat) : List Plane := ((range x).filter fun y =>
  before x y && symp x y == 0).map fun y => (x,y)

def planes : List Plane := (range 64).flatMap planeRow

def framesOver (p : Plane) : List Frame := ((range p.2).filter fun z =>
  before p.1 z && before p.2 z && symp p.1 z == 0 && symp p.2 z == 0).map
    fun z => (p.1,p.2,z)

def frames : List Frame := planes.flatMap framesOver

def contains (f : Frame) (v : Nat) : Bool :=
  let (a,b,c) := f
  v == 0 || v == a || v == b || v == c || v == (a^^^b) ||
  v == (a^^^c) || v == (b^^^c) || v == (a^^^b^^^c)

def bit (x i : Nat) : Nat := (x >>> i) % 2
def col (f : Frame) (i : Nat) : Nat := bit f.1 i + 2*bit f.2.1 i + 4*bit f.2.2 i
def det (x y z : Nat) : Nat :=
  let pair (a b c : Nat) := bit x a * bit y b * bit z c
  (pair 0 1 2 + pair 1 2 0 + pair 2 0 1 + pair 2 1 0 +
   pair 0 2 1 + pair 1 0 2) % 2

def minor (f : Frame) (m : Nat) : Nat :=
  det (col f (3*bit m 0)) (col f (1+3*bit m 1)) (col f (2+3*bit m 2))
def pack4 (u v w z : Nat) := u+2*v+4*w+8*z

def plucker (f : Frame) : Nat :=
  let t := minor f
  pack4 (t 0) (t 6) (t 5) (t 3) +
    16*pack4 (t 7) (t 1) (t 2) (t 4)

def ordered (xs : List Nat) := List.insertionSort (· ≤ ·) xs
def pencil (catalog : List (Frame × Nat)) (p : Plane) : List Nat :=
  ordered ((catalog.filter fun row => contains row.1 p.1 && contains row.1 p.2).map Prod.snd)

def xpart (p : Nat) := p % 16
def zpart (p : Nat) := p / 16
def quad (p : Nat) := parity4 (xpart p &&& zpart p)
def mixed (p : Nat) : Nat := if xpart p != 0 && zpart p != 0 then 1 else 0

def targetPoints : List Nat := (range 256).filter fun p => p != 0 && quad p == 0
def violation (p r : Nat) : Bool :=
  let t := p ^^^ r
  quad t == 0 && ((mixed p + mixed r + mixed t + parity4 (zpart p &&& xpart r)) % 2 == 1)

def targetPencils : List (List Nat) := targetPoints.flatMap fun p =>
  (targetPoints.filter fun r => p < r && r < (p^^^r) && violation p r).map fun r => [p,r,p^^^r]

/-- The Pauli coordinates of the points agree, including multiplicities. -/
theorem points_match : (frames.map plucker).Perm targetPoints := by
  have hs : ordered (frames.map plucker) = ordered targetPoints := by decide +kernel
  calc
    _ ~ ordered (frames.map plucker) := (perm_insertionSort _ _).symm
    _ ~ targetPoints := by rw [hs]; exact perm_insertionSort _ _

/-- Every actual pencil is carried bijectively to an unsatisfied Pauli context. -/
theorem pencils_match :
    (planes.map (pencil (frames.map fun f => (f,plucker f)))).Perm targetPencils := by
  let src := planes.map (pencil (frames.map fun f => (f,plucker f)))
  have hs : insertionSort (· ≤ ·) src = insertionSort (· ≤ ·) targetPencils := by decide +kernel
  calc
    _ ~ insertionSort (· ≤ ·) src := (perm_insertionSort _ _).symm
    _ ~ targetPencils := by rw [hs]; exact perm_insertionSort _ _

end Quadric.Dual
