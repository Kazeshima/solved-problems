import Quadric.Action
import Quadric.Incidence
import Mathlib.Data.Fintype.EquivFin

namespace Quadric.Four
open Matrix Finset
attribute [local irreducible] points pairs lines bad violations

abbrev PolarPoint := {f : Dual.Frame // f ∈ Dual.frames.toFinset}
abbrev PolarLine := {z : Dual.Plane // z ∈ Dual.planes.toFinset}
abbrev ViolatedLine (s : Signing) := {l : Finset Lab // l ∈ violations s}

def polarIncident (f : PolarPoint) (z : PolarLine) : Prop :=
  Dual.contains f.val z.val.1 = true ∧ Dual.contains f.val z.val.2 = true

/-- Points are binary Lagrangian row spaces and lines are isotropic two-space pencils. -/
structure DWIso (s : Signing) where
  point : PolarPoint ≃ Point
  line : PolarLine ≃ ViolatedLine s
  incident (f : PolarPoint) (z : PolarLine) : (point f).val ∈ (line z).val ↔ polarIncident f z

private noncomputable def enumEquiv {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (f : α → β) (t : Finset β) (e : (xs.map f).toFinset=t)
    (hcard : xs.toFinset.card=t.card) : ↥xs.toFinset ≃ ↥t := by
  let g (x : ↥xs.toFinset) : ↥t :=
    ⟨f x.val,e ▸ List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,List.mem_toFinset.mp x.property,rfl⟩)⟩
  apply Equiv.ofBijective g
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro y
    have h : y.val ∈ (xs.map f).toFinset := e ▸ y.property
    obtain ⟨x,hx,he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact ⟨⟨x,List.mem_toFinset.mpr hx⟩,Subtype.ext he⟩
  · simpa only [Fintype.card_coe] using hcard

def geomPoint (f : Dual.Frame) := Dual.decode (Dual.plucker f)
def geomLine (z : Dual.Plane) := Dual.decodedLine (Dual.pencil
  (Dual.frames.map fun f => (f,Dual.plucker f)) z)

noncomputable def polarPointsEquiv : PolarPoint ≃ Point :=
  enumEquiv Dual.frames geomPoint (points 4) (by
    simpa only [List.map_map,Function.comp_def,geomPoint] using Dual.plucker_points)
    (by rw [points_card]; decide +kernel)

noncomputable def polarLinesEquiv : PolarLine ≃ ViolatedLine canonical :=
  enumEquiv Dual.planes geomLine (violations canonical) (by
    rw [violations_canonical]
    simpa only [List.map_map,Function.comp_def,geomLine] using Dual.plucker_pencils)
    (by rw [violations_canonical,witness_count]; decide +kernel)

theorem raw_incidence (f : PolarPoint) (z : PolarLine) :
    geomPoint f.val ∈ geomLine z.val ↔ polarIncident f z := by
  rw [geomLine,Dual.decodedLine,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨k,hk,he⟩
    unfold Dual.pencil Dual.ordered at hk
    obtain ⟨⟨u,v⟩,hc,hv⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp hk)
    obtain ⟨hmem,hab⟩ := List.mem_filter.mp hc
    obtain ⟨u',hu',huv⟩ := List.mem_map.mp hmem
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj huv
    subst k
    let uP : PolarPoint := ⟨u', List.mem_toFinset.mpr hu'⟩
    have hp : polarPointsEquiv uP = polarPointsEquiv f := Subtype.ext he
    have huf := congrArg Subtype.val (polarPointsEquiv.injective hp)
    simpa [polarIncident,←huf,uP] using Bool.and_eq_true_iff.mp hab
  · intro hi
    refine ⟨Dual.plucker f.val,?_,rfl⟩
    unfold Dual.pencil Dual.ordered
    apply (List.mem_insertionSort _).mpr
    refine List.mem_map.mpr ⟨(f.val,Dual.plucker f.val),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact List.mem_map.mpr ⟨f.val,List.mem_toFinset.mp f.property,rfl⟩
    · exact Bool.and_eq_true_iff.mpr hi

noncomputable def canonicalIso : DWIso canonical where
  point := polarPointsEquiv
  line := polarLinesEquiv
  incident := raw_incidence

noncomputable def permPoints (C : Clifford 4) : Point ≃ Point where
  toFun p := ⟨C.perm p.val,(C.map_point _).mpr p.property⟩
  invFun p := ⟨C.perm.symm p.val,(C.map_point _).mp (by simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv _ := Subtype.ext (C.perm.symm_apply_apply _)
  right_inv _ := Subtype.ext (C.perm.apply_symm_apply _)

noncomputable def permLines (C : Clifford 4) (s : Signing) :
    ViolatedLine s ≃ ViolatedLine (push C s) where
  toFun l := ⟨lineMap C l.val,by rw [←map_bad]; exact mem_image_of_mem _ l.property⟩
  invFun l := ⟨lineMap C.inv l.val,by
    have h := map_bad_subset C.inv (push C s) (mem_image_of_mem _ l.property)
    rwa [push_inv] at h⟩
  left_inv l := Subtype.ext (by simp [lineMap,Clifford.inv,image_image,Function.comp_def])
  right_inv l := Subtype.ext (by simp [lineMap,Clifford.inv,image_image,Function.comp_def])

noncomputable def transportIso (C : Clifford 4) {s : Signing} (I : DWIso s) : DWIso (push C s) where
  point := I.point.trans (permPoints C)
  line := I.line.trans (permLines C s)
  incident f z := by
    change C.perm (I.point f).val ∈ lineMap C (I.line z).val ↔ _
    simpa only [lineMap,mem_image,EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right] using I.incident f z

end Quadric.Four
