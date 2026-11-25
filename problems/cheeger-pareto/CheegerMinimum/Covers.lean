import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Tauto

/-! The set-theoretic obstruction to a cover by inclusion-maximal tight sets. -/
namespace CheegerPareto.Small

abbrev Compatible {n : ℕ} (s t : Finset (Fin n)) : Prop :=
  n / 2 < (s ∪ t).card ∧ (s ∩ t).Nonempty ∧ (s ∪ t).card ≠ n - n / 2

private theorem outside {n : ℕ} {s : Finset (Fin n)} (hs : s.card < n) :
    ∃ x : Fin n, x ∉ s := by
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (s := s) (t := Finset.univ) (by simpa using hs)
  exact ⟨x, (Finset.mem_sdiff.mp hx).2⟩

private abbrev Block := Finset (Fin 8)

private theorem singleton_inter {a b : Block} {p : Fin 8}
    (hc : (a ∩ b).card = 1) (ha : p ∈ a) (hb : p ∈ b) : a ∩ b = {p} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · simpa using Finset.mem_inter.mpr ⟨ha, hb⟩
  · simp [hc]

private theorem four_in_three {d : Block} {a b c x : Fin 8}
    (hd : d.card = 3) (ha : a ∈ d) (hb : b ∈ d) (hc : c ∈ d) (hx : x ∈ d)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (ax : a ≠ x) (bx : b ≠ x) (cx : c ≠ x) :
    False := by
  have sub : ({a,b,c,x} : Block) ⊆ d := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have bound := Finset.card_le_card sub
  simp [ab, ac, bc, ax, bx, cx, hd] at bound

/-- Three pairwise meeting triples cover at most seven points. A fourth triple
covering an outside point must hit two of the first three at the same point. -/
private theorem fourth (F : Block → Prop)
    (covered : ∀ x, ∃ a, F a ∧ x ∈ a) (three : ∀ a, F a → a.card = 3)
    (linear : ∀ a b, F a → F b → a ≠ b → (a ∩ b).card = 1)
    (a b c : Block) (ga : F a) (gb : F b) (gc : F c)
    (ab : a ≠ b) (ac : a ≠ c) :
    ∃ d, F d ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      ∃ p ∈ d, (p ∈ a ∧ p ∈ b) ∨ (p ∈ a ∧ p ∈ c) ∨ (p ∈ b ∧ p ∈ c) := by
  have ca := three a ga
  have cb := three b gb
  have cc := three c gc
  have cab := linear a b ga gb ab
  have cac := linear a c ga gc ac
  have cu := Finset.card_union_add_card_inter a b
  have cv := Finset.card_union_add_card_inter (a ∪ b) c
  have ci : (a ∩ c).card ≤ ((a ∪ b) ∩ c).card :=
    Finset.card_le_card (by intro v hv; simp only [Finset.mem_inter, Finset.mem_union] at *; tauto)
  obtain ⟨x, hout⟩ := outside (s := a ∪ b ∪ c) (by omega)
  have xa : x ∉ a := fun h => hout (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have xb : x ∉ b := fun h => hout (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have xc : x ∉ c := fun h => hout (Finset.mem_union_right _ h)
  obtain ⟨d, gd, xd⟩ := covered x
  have ad : a ≠ d := fun he => xa (he ▸ xd)
  have bd : b ≠ d := fun he => xb (he ▸ xd)
  have cd : c ≠ d := fun he => xc (he ▸ xd)
  refine ⟨d, gd, ad, bd, cd, ?_⟩
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (a ∩ d).card by rw [linear a d ga gd ad]; decide)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (b ∩ d).card by rw [linear b d gb gd bd]; decide)
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (show 0 < (c ∩ d).card by rw [linear c d gc gd cd]; decide)
  obtain ⟨ia, id'⟩ := Finset.mem_inter.mp hi
  obtain ⟨jb, jd⟩ := Finset.mem_inter.mp hj
  obtain ⟨lc, ld⟩ := Finset.mem_inter.mp hl
  by_cases ij : i = j
  · exact ⟨i, id', Or.inl ⟨ia, ij ▸ jb⟩⟩
  by_cases il : i = l
  · exact ⟨i, id', Or.inr (Or.inl ⟨ia, il ▸ lc⟩)⟩
  by_cases jl : j = l
  · exact ⟨j, jd, Or.inr (Or.inr ⟨jb, jl ▸ lc⟩)⟩
  exact (four_in_three (three d gd) id' jd ld xd ij il jl
    (fun he => xa (he ▸ ia)) (fun he => xb (he ▸ jb)) (fun he => xc (he ▸ lc))).elim

/-- A pairwise linearly intersecting family of triples cannot have union of size eight. -/
theorem no_triple_cover_eight (F : Block → Prop)
    (covered : ∀ x, ∃ a, F a ∧ x ∈ a) (three : ∀ a, F a → a.card = 3)
    (linear : ∀ a b, F a → F b → a ≠ b → (a ∩ b).card = 1) : False := by
  have star : ∃ a b c : Block, ∃ p : Fin 8, F a ∧ F b ∧ F c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      p ∈ a ∧ p ∈ b ∧ p ∈ c := by
    obtain ⟨a, ga, _⟩ := covered 0
    obtain ⟨x, xa⟩ := outside (s := a) (by rw [three a ga]; decide)
    obtain ⟨b, gb, xb⟩ := covered x
    have ab : a ≠ b := fun he => xa (he ▸ xb)
    have c1 := three a ga
    have c2 := three b gb
    have sz := Finset.card_union_add_card_inter a b
    obtain ⟨y, hy⟩ := outside (s := a ∪ b) (by omega)
    obtain ⟨c, gc, yc⟩ := covered y
    have ac : a ≠ c := fun he => hy (Finset.mem_union_left _ (he ▸ yc))
    have bc : b ≠ c := fun he => hy (Finset.mem_union_right _ (he ▸ yc))
    obtain ⟨d, gd, ad, bd, cd, p, pd, hp⟩ := fourth F covered three linear a b c ga gb gc ab ac
    rcases hp with ⟨pa,pb⟩ | ⟨pa,pc⟩ | ⟨pb,pc⟩
    · exact ⟨a,b,d,p,ga,gb,gd,ab,ad,bd,pa,pb,pd⟩
    · exact ⟨a,c,d,p,ga,gc,gd,ac,ad,cd,pa,pc,pd⟩
    · exact ⟨b,c,d,p,gb,gc,gd,bc,bd,cd,pb,pc,pd⟩
  obtain ⟨a,b,c,p,ga,gb,gc,ab,ac,bc,pa,pb,pc⟩ := star
  obtain ⟨d,gd,ad,bd,cd,q,qd,hq⟩ := fourth F covered three linear a b c ga gb gc ab ac
  have iab := singleton_inter (linear a b ga gb ab) pa pb
  have iac := singleton_inter (linear a c ga gc ac) pa pc
  have ibc := singleton_inter (linear b c gb gc bc) pb pc
  have same : q = p := by
    rcases hq with hq | hq | hq
    · simpa [iab] using (show q ∈ a ∩ b from Finset.mem_inter.mpr hq)
    · simpa [iac] using (show q ∈ a ∩ c from Finset.mem_inter.mpr hq)
    · simpa [ibc] using (show q ∈ b ∩ c from Finset.mem_inter.mpr hq)
  have pd : p ∈ d := same ▸ qd
  have iad := singleton_inter (linear a d ga gd ad) pa pd
  have ibd := singleton_inter (linear b d gb gd bd) pb pd
  have icd := singleton_inter (linear c d gc gd cd) pc pd
  have first := Finset.card_union_add_card_inter a b
  have second := Finset.card_union_add_card_inter (a ∪ b) c
  have third := Finset.card_union_add_card_inter (a ∪ b ∪ c) d
  simp only [Finset.union_inter_distrib_right, iab, iac, ibc, iad, ibd, icd,
    Finset.union_idempotent, Finset.card_singleton, three a ga, three b gb,
    three c gc, three d gd] at first second third
  have bound : (a ∪ b ∪ c ∪ d).card ≤ 8 := by
    simpa using Finset.card_le_card (Finset.subset_univ (a ∪ b ∪ c ∪ d))
  omega

/-- The obstruction is independent of the graph and of the real coordinate values. -/
theorem no_small_cover {n : ℕ} (lo : 2 ≤ n) (hi : n ≤ 9)
    (F : Finset (Fin n) → Prop) (covered : ∀ x, ∃ a, F a ∧ x ∈ a)
    (small : ∀ a, F a → a.card < n / 2)
    (compatible : ∀ a b, F a → F b → a ≠ b → Compatible a b) : False := by
  have other (a) (ga : F a) : ∃ b, F b ∧ a ≠ b := by
    have ha := small a ga
    obtain ⟨v, hv⟩ := outside (s := a) (by omega)
    obtain ⟨b, gb, h⟩ := covered v
    exact ⟨b, gb, fun he => hv (he ▸ h)⟩
  have shape (a b) (ga : F a) (gb : F b) (ab : a ≠ b) :
      n = 8 ∧ a.card = 3 ∧ (a ∩ b).card = 1 := by
    obtain ⟨big, meet, comp⟩ := compatible a b ga gb ab
    have hp := Finset.card_pos.mpr meet
    have ha := small a ga
    have hb := small b gb
    have eq := Finset.card_union_add_card_inter a b
    omega
  obtain ⟨a, ga, _⟩ := covered ⟨0, by omega⟩
  obtain ⟨b, gb, ab⟩ := other a ga
  obtain ⟨rfl, _⟩ := shape a b ga gb ab
  apply no_triple_cover_eight F covered
  · intro s hs
    obtain ⟨t, ht, st⟩ := other s hs
    exact (shape s t hs ht st).2.1
  · intro s t hs ht st
    exact (shape s t hs ht st).2.2

end CheegerPareto.Small
