import Quadric.Five.OneBlock

namespace Quadric.Five.Census.Block
open Packing
def Interval (f : ℕ→Bool) (start n : ℕ) := ∀ j<n,f (start+j)=true
def testInterval (f : ℕ→Bool) (start n : ℕ) := (List.range n).all (fun j=>f (start+j))
theorem interval_checked {f : ℕ→Bool} {s n : ℕ} (h : testInterval f s n=true) : Interval f s n :=
  fun _ hj=>List.all_eq_true.mp h _ (List.mem_range.mpr hj)
theorem Interval.join {f : ℕ→Bool} {s n k : ℕ} (h : Interval f s n) (z : Interval f (s+n) k) :
    Interval f s (n+k) := by
  intro j hj
  by_cases lo : j<n
  · exact h j lo
  · have h':=z (j-n) (by omega); simpa only [show s+n+(j-n)=s+j by omega] using h'

def crossCheck (S : Split) (tc : Tables) (a : ℕ) := packedLE 10 ((crossMinimumA S a)*ones 10) (vec S.crossBlock tc a)
def shapeOK (S : Split) :=
  S.first.lowWidth==10 && S.second.lowWidth==10 && S.crossBlock.lowWidth==10 &&
  S.lowFirst.length==1024 && S.cutoff<512 && S.high.length+size S.first+size S.second+size S.crossBlock≤511 &&
  S.lowFirst.all (·≤511)
theorem prepare_parts (S : Split) (tc : Tables) (shape : shapeOK S=true) (h : Interval (crossCheck S tc) 0 1024) :
    prepared S tc=true :=
  Bool.and_eq_true_iff.mpr ⟨shape,List.all_eq_true.mpr (fun a ha=>by simpa only [Nat.zero_add] using h a (List.mem_range.mp ha))⟩
def Segment (S : Split) (ta tb tc : Tables) (h n : ℕ) (xs : List Row) :=
  xs.length=n ∧ run S ta tb tc h xs=true

theorem Segment.join {S : Split} {ta tb tc : Tables} {h n k : ℕ} {xs ys : List Row}
    (a : Segment S ta tb tc h n xs) (b : Segment S ta tb tc (h+n) k ys) :
    Segment S ta tb tc h (n+k) (xs++ys) := by
  refine ⟨by rw [List.length_append,a.1,b.1],?_⟩
  rw [run_append,a.1,a.2,b.2]; rfl

end Quadric.Five.Census.Block
