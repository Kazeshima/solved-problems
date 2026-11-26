import Quadric.HeavyPhase
import Quadric.Profiles
import Quadric.Incidence

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators
attribute [local irreducible] points pairs lines bad violations level height

theorem push_mul (C B : Clifford 4) (s : Signing) :
    push (C.mul B) s = push C (push B s) := by
  apply matrix_injective
  simp only [matrix_push,Clifford.conj,Clifford.mul,transpose_mul]
  noncomm_ring

theorem translate_level (a : W) (o : Opt) (x : W) :
    level (optMove (Clifford.translation a) o) x = level o (x+a) := by
  obtain ⟨u,_,hu⟩ := state_ray o
  have h1 := weight_of_ray (move_ray_formula (Clifford.translation a) hu) x
  have h2 := weight_of_ray hu (x+a)
  have hv : ((Clifford.translation a).U *ᵥ u) x=u (x+a) := by
    change (pauli (a,0) *ᵥ u) x=_; simp [pauli_apply_vec]
  rw [hv] at h1
  have ht := h1.trans h2.symm
  change weight (optMove (Clifford.translation a) o).val x = _ at ht
  rw [level_spec,level_spec] at ht
  exact Fin.ext (by exact_mod_cast ht)

theorem translate_involutive (a : W) : Function.Involutive (optMove (Clifford.translation a)) := by
  intro o
  apply Subtype.ext
  apply matrix_injective
  change matrixOf (push _ (push _ o.val))=_
  rw [matrix_push,matrix_push]
  let C := Clifford.translation a
  have ht : C.Uᵀ=C.U := by
    change (pauli (a,0))ᵀ=_; simp [pauli_transpose,q]; rfl
  have hi : C.U*C.U=1 := by simpa [ht] using C.leftInv
  change C.U*(C.U*matrixOf o.val*C.Uᵀ)*C.Uᵀ=_
  rw [ht]
  calc _ = (C.U*C.U)*matrixOf o.val*(C.U*C.U) := by noncomm_ring
       _ = _ := by rw [hi,one_mul,mul_one]

theorem heavy_wave (o : Opt) (ho : level o 0=9) :
    ∃ f : Quadratics, o.val=push (phaseGate f) canonical := by
  classical
  obtain ⟨u,_,hu⟩ := state_ray o
  have h0 : 8*(u 0)^2=3 := by
    have hz := (weight_of_ray hu 0).symm.trans (level_spec o 0)
    rw [ho] at hz; change 24*(u 0)^2=9 at hz; linarith
  let w (x : W) := 8*u 0*u x
  have w0 : w 0=3 := by dsimp [w]; linarith only [h0]
  have wsmall (x : W) (hx : x≠0) : w x ^ 2=1 := by
    have hh := (weight_of_ray hu x).symm.trans (level_spec o x)
    rw [nine_others ho hx] at hh
    norm_num at hh
    dsimp [w]
    linear_combination (8*(u x)^2)*h0 + hh
  let f (x : W) : Bit := if w x=v x then 0 else 1
  have f0 : f 0=0 := by simp [f,w0,v]
  have hfw (x : W) : wave f x=w x := by
    by_cases h : w x=v x
    · simp [wave,f,h]
    · have hx : x≠0 := by rintro rfl; exact h (by simp [w0,v])
      have hw := wsmall x hx
      have hn : w x ≠ -1 := by simpa [v,hx] using h
      have ha : w x=1 := by
        rcases (sq_eq_one_iff.mp hw) with h1|h1
        · exact h1
        · contradiction
      rw [wave,show f x=1 from if_neg h,chi_one,ha]; simp [v,hx]
  have hm : matrixOf o.val=waveMatrix f := by
    rw [hu]
    ext i j
    simp only [waveMatrix,ray,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,hfw,w]
    linear_combination (-16*u i*u j)*h0
  let F : Quadratics := ⟨f,wave_quadratic f0 hm⟩
  refine ⟨F,matrix_injective (hm.trans (phase_image F).symm)⟩

abbrev HeavyAt (x : W) := {o : Opt // level o x=9}
noncomputable instance (x : W) : Fintype (HeavyAt x) := Fintype.ofFinite _
noncomputable def atOrigin (f : Quadratics) : HeavyAt 0 :=
  ⟨optMove (phaseGate f) canonicalOpt,by
    let s := optMove (phaseGate f) canonicalOpt
    have h := wave_weight f.val s.val (phase_image f) 0
    change weight s.val 0 = _ at h
    rw [level_spec] at h; norm_num [v] at h
    exact Fin.ext (by exact_mod_cast h)⟩

theorem atOrigin_val (f : Quadratics) : (atOrigin f).val.val = push (phaseGate f) canonical := rfl

theorem origin_bijective : Function.Bijective atOrigin := by
  constructor
  · intro f g he
    apply Subtype.ext
    apply wave_inj f.property.1 g.property.1
    rw [←phase_image f,←phase_image g]
    have hsign := congrArg (fun t : HeavyAt 0 => t.val.val) he
    simp only [atOrigin_val] at hsign
    exact congrArg matrixOf hsign
  · intro o
    obtain ⟨f,hf⟩ := heavy_wave o.val o.property
    exact ⟨f,Subtype.ext (Subtype.ext hf.symm)⟩

noncomputable def relocate (x : W) : HeavyAt 0 ≃ HeavyAt x where
  toFun s := ⟨optMove (Clifford.translation x) s.val,by simpa [translate_level] using s.property⟩
  invFun s := ⟨optMove (Clifford.translation x) s.val,by simpa [translate_level] using s.property⟩
  left_inv s := Subtype.ext (translate_involutive x s.val)
  right_inv s := Subtype.ext (translate_involutive x s.val)

theorem heavy_at_count (x : W) : Fintype.card (HeavyAt x)=1024 := by
  rw [←Fintype.card_congr (relocate x),←Fintype.card_congr (Equiv.ofBijective atOrigin origin_bijective),phase_count]

/-- Orbit membership on precisely the 135 labelled signs, with a real orthogonal Pauli normalizer. -/
def InCanonicalOrbit (s : Signing) : Prop := ∃ C : Clifford 4, push C canonical=s

theorem undo_move (C : Clifford 4) (s : Signing) (h : InCanonicalOrbit (push C s)) :
    InCanonicalOrbit s := by
  obtain ⟨B,hB⟩ := h
  exact ⟨C.inv.mul B,by rw [push_mul,hB,push_inv]⟩

theorem heavy_orbit {s : Opt} (h : height s=9) : InCanonicalOrbit s.val := by
  obtain ⟨x,hx⟩ := heavy_exists s
  let C := Clifford.translation x
  have hh : level (optMove C s) 0=9 := by rw [translate_level,zero_add,hx,h]
  obtain ⟨f,hf⟩ := heavy_wave _ hh
  exact undo_move C _ ⟨phaseGate f,hf.symm⟩

theorem middle_orbit {s : Opt} (h : height s=8) : InCanonicalOrbit s.val := by
  classical
  obtain ⟨x,hx⟩ := heavy_exists s
  have h8 := hx.trans h
  obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (univ.filter fun y => level s y=2).card by rw [count_light h8]; decide)
  have h2 := (mem_filter.mp hy).2
  have hn : x≠y := by rintro rfl; rw [h8] at h2; contradiction
  let a : Direction := ⟨x+y,mt (word_zero x y).mp hn⟩
  have hr : x+a.val=y := by dsimp [a]; simp [←add_assoc]
  have hh := (step_eight h8 a).1.mpr (hr ▸ h2)
  exact undo_move (mixGate a) _ (heavy_orbit hh)

theorem every_optimum_in_orbit (s : Opt) : InCanonicalOrbit s.val := by
  rcases profiles s with h|h|h
  · exact heavy_orbit h
  · exact middle_orbit h
  · let a : Direction := ⟨axis 0,by intro hz; have := congrFun hz 0; simpa [axis] using this⟩
    exact undo_move (mixGate a) _ (middle_orbit (step_four a h))

theorem optimum_incidence (s : Opt) : ∃ C : Clifford 4, push C canonical=s.val ∧
    (points 4).image C.perm=points 4 ∧
    ((Dual.planes.map (Dual.pencil (Dual.frames.map fun f => (f,Dual.plucker f)))).map
      (fun l => lineMap C (Dual.decodedLine l))).toFinset = violations s.val := by
  obtain ⟨C,hc⟩ := every_optimum_in_orbit s
  refine ⟨C,hc,?_,?_⟩
  · ext p; constructor
    · rintro hh; obtain ⟨e,he,rfl⟩ := mem_image.mp hh; exact (C.map_point _).mpr he
    · intro he; exact mem_image.mpr ⟨C.perm.symm p,
        (C.map_point _).mp (by simpa using he), C.perm.apply_symm_apply _⟩
  · rw [←hc,←map_bad,violations_canonical,←Dual.plucker_pencils]
    let xs := Dual.planes.map (Dual.pencil (Dual.frames.map fun f => (f,Dual.plucker f)))
    have mapset (ls : List (Finset Lab)) : (ls.map (lineMap C)).toFinset = ls.toFinset.image (lineMap C) := by
      ext l; simp
    simpa only [List.map_map,Function.comp_def,xs] using mapset (xs.map Dual.decodedLine)

end Quadric.Four
