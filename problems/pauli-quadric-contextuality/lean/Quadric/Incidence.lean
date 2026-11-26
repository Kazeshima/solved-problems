import Quadric.Geometry
import Quadric.Chart

namespace Quadric.Dual
open Finset
open Quadric.Four
attribute [local irreducible] bad pairs points lines targetPoints targetPencils frames planes

def decode (k : ℕ) : Label 4 :=
  (fun i => (bit (xpart k) i.val : Bit), fun i => (bit (zpart k) i.val : Bit))

def decodedLine (t : List ℕ) := (t.map decode).toFinset

def signedTriple : List ℕ → Bool
  | [a,b,c] =>
    let p := decode a
    let r := decode b
    decide ((p ≠ 0 ∧ q p=0) ∧ (r ≠ 0 ∧ q r=0) ∧ (p+r ≠ 0 ∧ q (p+r)=0) ∧
      decode c = p+r ∧ negativeBit p + negativeBit r + negativeBit (p+r) + cross p r = 1)
  | _ => false

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

private theorem all_signed : targetPencils.all signedTriple = true := by decide +kernel

private theorem decoded_mem {t : List ℕ} (h : t ∈ targetPencils) :
    decodedLine t ∈ bad Four.mixed := by
  have hh := List.all_eq_true.mp all_signed t h
  cases t with
  | nil => simp [signedTriple] at hh
  | cons a t =>
    cases t with
    | nil => simp [signedTriple] at hh
    | cons b t =>
      cases t with
      | nil => simp [signedTriple] at hh
      | cons c t =>
        cases t with
        | cons k ks => simp [signedTriple] at hh
        | nil =>
          simp only [signedTriple, decide_eq_true_eq] at hh
          obtain ⟨hp,hr,ht,he,hs⟩ := hh
          let p := decode a
          let r := decode b
          have hpair : (p,r) ∈ pairs 4 := (@mem_pairs 4 p r).mpr
            ⟨(@mem_points 4 p).mpr hp,(@mem_points 4 r).mpr hr,
             (@mem_points 4 (p+r)).mpr ht⟩
          simpa [decodedLine,triple,he] using @bad_of_bits p r hpair hs

def encodeWord (a : Word 4) : ℕ := (a 0).val + 2*(a 1).val + 4*(a 2).val + 8*(a 3).val
def encode (p : Label 4) : ℕ := encodeWord p.1 + 16*encodeWord p.2
def encodeLine (l : Finset (Label 4)) : ℕ := ∑ p ∈ l, 2^(encode p)
def rawKey (t : List ℕ) : ℕ := (t.map fun k => 2^k).sum

private theorem card_from_keys {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    (xs : List ι) (f : ι → α) (g : α → β) (k : ι → β)
    (h : ∀ x ∈ xs, g (f x) = k x) :
    (xs.map k).toFinset.card ≤ (xs.map f).toFinset.card := by
  have incl : (xs.map k).toFinset ⊆ (xs.map f).toFinset.image g := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    exact mem_image.mpr ⟨f x,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),h x hx⟩
  exact (card_le_card incl).trans card_image_le

/-- The principal-minor point map reaches the exact point set used in Claim A. -/
theorem plucker_points :
    ((frames.map plucker).map decode).toFinset = points 4 := by
  apply (List.toFinset_eq_of_perm _ _ (points_match.map decode)).trans
  have incl : (targetPoints.map decode).toFinset ⊆ points 4 := by
    intro p hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hall : targetPoints.all (fun k => decide (decode k ≠ 0 ∧ q (decode k) = 0)) = true := by
      decide +kernel
    exact mem_points.mpr (of_decide_eq_true (List.all_eq_true.mp hall k hk))
  apply eq_of_subset_of_card_le incl
  rw [points_card]
  have roundtrip : targetPoints.all (fun k => decide (encode (decode k)=k)) = true := by decide +kernel
  have lb := card_from_keys targetPoints decode encode id
    (fun k hk => of_decide_eq_true (List.all_eq_true.mp roundtrip k hk))
  exact (by decide +kernel : 135 ≤ (targetPoints.map id).toFinset.card).trans lb

/-- Images of precisely the pencils through isotropic two-spaces, in the same unordered-line
type and with the same Pauli violation predicate as the all-rank theorem. -/
theorem plucker_pencils :
    ((planes.map (pencil (frames.map fun f => (f,plucker f)))).map decodedLine).toFinset
      = bad Four.mixed := by
  apply (List.toFinset_eq_of_perm _ _ (pencils_match.map decodedLine)).trans
  have incl : (targetPencils.map decodedLine).toFinset ⊆ bad Four.mixed := by
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    exact decoded_mem hk
  apply eq_of_subset_of_card_le incl
  rw [witness_count]
  have roundtrip : targetPencils.all (fun t => decide (encodeLine (decodedLine t)=rawKey t)) = true :=
    by decide +kernel
  have lb := card_from_keys targetPencils decodedLine encodeLine rawKey
    (fun t ht => of_decide_eq_true (List.all_eq_true.mp roundtrip t ht))
  exact (by decide +kernel : 315 ≤ (targetPencils.map rawKey).toFinset.card).trans lb

end Quadric.Dual
