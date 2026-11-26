import ZonotopeFlips.DDCount

/-!
# Flips at a pair of vertices

A *flip* at the pair `i < j` is a consistent graph `G` not containing the edge `ij` such that
`G + ij` is consistent as well.  This file shows that the flips at `ij` are exactly the graphs
of the four classes `DD`, `DU`, `UD`, `UU`, and that complementation matches `DD` with `UU`
and `DU` with `UD`.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

/-! ### Complement (of `G + ij`) -/

/-- The complement of `G + ij` inside the complete graph on `S`. -/
def cmpl (S : Finset ℕ) (i j : ℕ) (G : Graph) : Graph := (pairs S \ G).erase (i, j)

theorem cmpl_mem_graphs {S : Finset ℕ} {i j : ℕ} {G : Graph} : cmpl S i j G ∈ graphs S := by
  rw [mem_graphs]
  intro p hp
  unfold cmpl at hp
  exact (mem_sdiff.mp (mem_of_mem_erase hp)).1

theorem adj_cmpl {S : Finset ℕ} {i j : ℕ} {G : Graph} (hG : G ∈ graphs S) (hij : i < j)
    {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    adj (cmpl S i j G) x y ↔ ¬ adj G x y ∧ ¬ (x = i ∧ y = j) ∧ ¬ (x = j ∧ y = i) := by
  have key : ∀ u v, u ∈ S → v ∈ S → u < v →
      ((u, v) ∈ cmpl S i j G ↔ ¬ adj G u v ∧ ¬ (u = i ∧ v = j)) := by
    intro u v hu hv huv
    unfold cmpl
    rw [mem_erase, mem_sdiff, mem_pairs, mem_iff_adj hG huv, Ne, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, ⟨hu, hv, huv⟩, h1⟩
  have nomem : ∀ u v, u < v → (v, u) ∉ cmpl S i j G := by
    intro u v huv h
    unfold cmpl at h
    have := mem_pairs.mp (mem_sdiff.mp (mem_of_mem_erase h)).1
    omega
  show ((x, y) ∈ cmpl S i j G ∨ (y, x) ∈ cmpl S i j G) ↔ _
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · constructor
    · rintro (h1 | h1)
      · have := (key x y hx hy h).mp h1
        exact ⟨this.1, this.2, by omega⟩
      · exact absurd h1 (nomem x y h)
    · rintro ⟨h1, h2, _⟩
      exact Or.inl ((key x y hx hy h).mpr ⟨h1, h2⟩)
  · constructor
    · rintro (h1 | h1)
      · exact absurd h1 (nomem y x h)
      · have := (key y x hy hx h).mp h1
        exact ⟨fun h' => this.1 (adj_comm.mp h'), by omega, fun h' => this.2 ⟨h'.2, h'.1⟩⟩
    · rintro ⟨h1, _, h3⟩
      exact Or.inr ((key y x hy hx h).mpr
        ⟨fun h' => h1 (adj_comm.mp h'), fun h' => h3 ⟨h'.2, h'.1⟩⟩)

theorem cmpl_cmpl {S : Finset ℕ} {i j : ℕ} {G : Graph} (hG : G ∈ graphs S) (hij : i < j)
    (hnot : ¬ adj G i j) : cmpl S i j (cmpl S i j G) = G := by
  apply graph_ext cmpl_mem_graphs hG
  intro x hx y hy hxy
  rw [adj_cmpl cmpl_mem_graphs hij hx hy (by omega), adj_cmpl hG hij hx hy (by omega)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_contra h4
    exact h1 ⟨h4, h2, h3⟩
  · intro h
    refine ⟨fun h' => h'.1 h, ?_, ?_⟩
    · rintro ⟨h1, h2⟩
      exact hnot (h1 ▸ h2 ▸ h)
    · rintro ⟨h1, h2⟩
      omega

theorem MonoP.not {S : Finset ℕ} {p : ℕ} {a : ℕ → Prop} (h : MonoP S p a) :
    MonoP S p (fun q => ¬ a q) := by
  rcases h with h | h
  · right
    intro x hx y hy hxp hyp hxy hnx hy'
    exact hnx (h x hx y hy hxp hyp hxy hy')
  · left
    intro x hx y hy hxp hyp hxy hny hx'
    exact hny (h x hx y hy hxp hyp hxy hx')

theorem Cls.cmpl {S : Finset ℕ} {i j : ℕ} {φi φj ψi ψj : ℕ → Prop} {G : Graph}
    (hG : G ∈ graphs S) (hc : Cls S i j φi φj G) (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hψi : ∀ q ∈ S, (ψi q ↔ (q ≠ i ∧ q ≠ j ∧ ¬ φi q)))
    (hψj : ∀ q ∈ S, (ψj q ↔ (q ≠ j ∧ q ≠ i ∧ ¬ φj q)))
    (hmi : MonoP S i ψi) (hmj : MonoP S j ψj) :
    Cls S i j ψi ψj (ZonoFlips.cmpl S i j G) := by
  have rowi : ∀ q ∈ S, (adj (ZonoFlips.cmpl S i j G) i q ↔ ψi q) := by
    intro q hq
    rw [hψi q hq]
    by_cases hqi : q = i
    · constructor
      · intro h; exact absurd hqi.symm (adj_mem cmpl_mem_graphs h).2.2
      · intro h; exact absurd hqi h.1
    · rw [adj_cmpl hG hij hi hq (Ne.symm hqi), hc.rowi q hq]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨hqi, fun e => h2 ⟨rfl, e⟩, h1⟩
      · rintro ⟨_, h2, h3⟩; exact ⟨h3, fun e => h2 e.2, fun e => by omega⟩
  have rowj : ∀ q ∈ S, (adj (ZonoFlips.cmpl S i j G) j q ↔ ψj q) := by
    intro q hq
    rw [hψj q hq]
    by_cases hqj : q = j
    · constructor
      · intro h; exact absurd hqj.symm (adj_mem cmpl_mem_graphs h).2.2
      · intro h; exact absurd hqj h.1
    · rw [adj_cmpl hG hij hj hq (Ne.symm hqj), hc.rowj q hq]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨hqj, fun e => h3 ⟨rfl, e⟩, h1⟩
      · rintro ⟨_, h2, h3⟩; exact ⟨h3, fun e => by omega, fun e => h2 e.2⟩
  refine ⟨?_, rowi, rowj⟩
  intro p hp
  by_cases hpi : p = i
  · rw [hpi]; exact hmi.congr (fun q hq _ => rowi q hq)
  by_cases hpj : p = j
  · rw [hpj]; exact hmj.congr (fun q hq _ => rowj q hq)
  refine (hc.cons p hp).not.congr ?_
  intro q hq hqp
  rw [adj_cmpl hG hij hp hq (Ne.symm hqp)]
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, fun e => hpi e.1, fun e => hpj e.1⟩

/-- Complementation is a bijection between two classes with complementary prescriptions. -/
theorem card_cls_cmpl {S : Finset ℕ} {i j : ℕ} {φi φj ψi ψj : ℕ → Prop}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) (hφ : ¬ φi j) (hψ : ¬ ψi j)
    (hψi : ∀ q ∈ S, (ψi q ↔ (q ≠ i ∧ q ≠ j ∧ ¬ φi q)))
    (hψj : ∀ q ∈ S, (ψj q ↔ (q ≠ j ∧ q ≠ i ∧ ¬ φj q)))
    (hφi : ∀ q ∈ S, (φi q ↔ (q ≠ i ∧ q ≠ j ∧ ¬ ψi q)))
    (hφj : ∀ q ∈ S, (φj q ↔ (q ≠ j ∧ q ≠ i ∧ ¬ ψj q)))
    (hmφi : MonoP S i φi) (hmφj : MonoP S j φj) (hmψi : MonoP S i ψi) (hmψj : MonoP S j ψj) :
    (clsSet S i j φi φj).card = (clsSet S i j ψi ψj).card := by
  apply Finset.card_nbij' (cmpl S i j) (cmpl S i j)
  · intro G hG
    have h := mem_clsSet.mp hG
    exact mem_clsSet.mpr ⟨cmpl_mem_graphs, h.2.cmpl h.1 hi hj hij hψi hψj hmψi hmψj⟩
  · intro G hG
    have h := mem_clsSet.mp hG
    exact mem_clsSet.mpr ⟨cmpl_mem_graphs, h.2.cmpl h.1 hi hj hij hφi hφj hmφi hmφj⟩
  · intro G hG
    have h := mem_clsSet.mp hG
    exact cmpl_cmpl h.1 hij (fun h' => hφ ((h.2.rowi j hj).mp h'))
  · intro G hG
    have h := mem_clsSet.mp hG
    exact cmpl_cmpl h.1 hij (fun h' => hψ ((h.2.rowi j hj).mp h'))

theorem card_UU {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) :
    (clsSet S i j (iU j) (jU i j)).card = (clsSet S i j (iD i j) (jD i)).card := by
  symm
  apply card_cls_cmpl hi hj hij (by arith) (by arith) _ _ _ _
    (mono_iD S i j) (mono_jD S i j) (mono_iU S i j) (mono_jU S i j)
  · intro q _; arith
  · intro q _; arith
  · intro q _; arith
  · intro q _; arith

theorem card_UD {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) :
    (clsSet S i j (iU j) (jD i)).card = (clsSet S i j (iD i j) (jU i j)).card := by
  symm
  apply card_cls_cmpl hi hj hij (by arith) (by arith) _ _ _ _
    (mono_iD S i j) (mono_jU S i j) (mono_iU S i j) (mono_jD S i j)
  · intro q _; arith
  · intro q _; arith
  · intro q _; arith
  · intro q _; arith

/-! ### Flips are exactly the four classes -/

/-- `G` and `G + ij` are both consistent, and `ij` is not an edge of `G`. -/
def IsFlip (S : Finset ℕ) (i j : ℕ) (G : Graph) : Prop :=
  Consistent S G ∧ (i, j) ∉ G ∧ Consistent S (insert (i, j) G)

/-- The flips at the pair `i < j`, recorded by their smaller graph. -/
def flipSet (S : Finset ℕ) (i j : ℕ) : Finset Graph := sel S (IsFlip S i j)

theorem adj_insert {G : Graph} {i j x y : ℕ} :
    adj (insert (i, j) G) x y ↔ adj G x y ∨ (x = i ∧ y = j) ∨ (x = j ∧ y = i) := by
  unfold adj
  simp only [mem_insert, Prod.mk.injEq]
  tauto

/-- If a row stays monotone after switching position `t` from `0` to `1`, then it is the
initial segment below `t` or the final segment above `t`. -/
theorem toggle {S : Finset ℕ} {p t : ℕ} {a : ℕ → Prop} (ht : t ∈ S) (htp : t ≠ p) (hat : ¬ a t)
    (h1 : MonoP S p a) (h2 : MonoP S p (fun q => a q ∨ q = t)) :
    (∀ q ∈ S, q ≠ p → (a q ↔ q < t)) ∨ (∀ q ∈ S, q ≠ p → (a q ↔ t < q)) := by
  rcases h1 with d1 | u1 <;> rcases h2 with d2 | u2
  · left
    intro q hq hqp
    constructor
    · intro haq
      by_contra hlt
      have : t < q := by
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact absurd h hlt
        · exact absurd (h ▸ haq) hat
        · exact h
      exact hat (d1 t ht q hq htp hqp this haq)
    · intro hlt
      rcases d2 q hq t ht hqp htp hlt (Or.inr rfl) with h | h
      · exact h
      · omega
  · have noabove : ∀ q ∈ S, q ≠ p → ¬ t < q := by
      intro q hq hqp hlt
      rcases u2 t ht q hq htp hqp hlt (Or.inr rfl) with h | h
      · exact hat (d1 t ht q hq htp hqp hlt h)
      · omega
    by_cases hex : ∃ x ∈ S, x ≠ p ∧ x < t ∧ a x
    · obtain ⟨x0, hx0, hx0p, hx0t, hax0⟩ := hex
      left
      intro q hq hqp
      constructor
      · intro haq
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact h
        · exact absurd (h ▸ haq) hat
        · exact absurd h (noabove q hq hqp)
      · intro hlt
        rcases Nat.lt_trichotomy q x0 with h | h | h
        · exact d1 q hq x0 hx0 hqp hx0p h hax0
        · rw [h]; exact hax0
        · rcases u2 x0 hx0 q hq hx0p hqp h (Or.inl hax0) with h' | h'
          · exact h'
          · omega
    · right
      intro q hq hqp
      constructor
      · intro haq
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact absurd ⟨q, hq, hqp, h, haq⟩ hex
        · exact absurd (h ▸ haq) hat
        · exact h
      · intro hlt
        exact absurd hlt (noabove q hq hqp)
  · have nobelow : ∀ q ∈ S, q ≠ p → ¬ q < t := by
      intro q hq hqp hlt
      rcases d2 q hq t ht hqp htp hlt (Or.inr rfl) with h | h
      · exact hat (u1 q hq t ht hqp htp hlt h)
      · omega
    by_cases hex : ∃ x ∈ S, x ≠ p ∧ t < x ∧ a x
    · obtain ⟨x0, hx0, hx0p, hx0t, hax0⟩ := hex
      right
      intro q hq hqp
      constructor
      · intro haq
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact absurd h (nobelow q hq hqp)
        · exact absurd (h ▸ haq) hat
        · exact h
      · intro hlt
        rcases Nat.lt_trichotomy q x0 with h | h | h
        · rcases d2 q hq x0 hx0 hqp hx0p h (Or.inl hax0) with h' | h'
          · exact h'
          · omega
        · rw [h]; exact hax0
        · exact u1 x0 hx0 q hq hx0p hqp h hax0
    · left
      intro q hq hqp
      constructor
      · intro haq
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact h
        · exact absurd (h ▸ haq) hat
        · exact absurd ⟨q, hq, hqp, h, haq⟩ hex
      · intro hlt
        exact absurd hlt (nobelow q hq hqp)
  · right
    intro q hq hqp
    constructor
    · intro haq
      by_contra hlt
      have : q < t := by
        rcases Nat.lt_trichotomy q t with h | h | h
        · exact h
        · exact absurd (h ▸ haq) hat
        · exact absurd h hlt
      exact hat (u1 q hq t ht hqp htp this haq)
    · intro hlt
      rcases u2 t ht q hq htp hqp hlt (Or.inr rfl) with h | h
      · exact h
      · omega

/-- In a flip the rows of `i` and `j` are of one of the two prescribed shapes each. -/
theorem rows_of_flip {S : Finset ℕ} {i j : ℕ} {G : Graph} (hG : G ∈ graphs S)
    (hi : i ∈ S) (hj : j ∈ S) (hij : i < j) (hf : IsFlip S i j G) :
    ((∀ q ∈ S, (adj G i q ↔ iD i j q)) ∨ (∀ q ∈ S, (adj G i q ↔ iU j q))) ∧
      ((∀ q ∈ S, (adj G j q ↔ jD i q)) ∨ (∀ q ∈ S, (adj G j q ↔ jU i j q))) := by
  obtain ⟨hc, hnot, hc'⟩ := hf
  have hnadj : ¬ adj G i j := fun h => hnot ((mem_iff_adj hG hij).mpr h)
  have hirr : ∀ p, ¬ adj G p p := fun p h => (adj_mem hG h).2.2 rfl
  constructor
  · have h2 : MonoP S i (fun q => adj G i q ∨ q = j) := by
      refine (hc' i hi).congr ?_
      intro q _ _
      rw [adj_insert]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · omega
    rcases toggle hj (by omega) hnadj (hc i hi) h2 with h | h
    · left
      intro q hq
      by_cases hqi : q = i
      · rw [hqi]; exact ⟨fun h' => absurd h' (hirr i), fun h' => by arith⟩
      · rw [h q hq hqi]; exact ⟨fun h' => by arith, fun h' => by arith⟩
    · right
      intro q hq
      by_cases hqi : q = i
      · rw [hqi]; exact ⟨fun h' => absurd h' (hirr i), fun h' => by arith⟩
      · rw [h q hq hqi]; exact ⟨fun h' => by arith, fun h' => by arith⟩
  · have h2 : MonoP S j (fun q => adj G j q ∨ q = i) := by
      refine (hc' j hj).congr ?_
      intro q _ _
      rw [adj_insert]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨rfl, h⟩)
      · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · omega
        · exact Or.inr h
    rcases toggle hi (by omega) (fun h => hnadj (adj_comm.mp h)) (hc j hj) h2 with h | h
    · left
      intro q hq
      by_cases hqj : q = j
      · rw [hqj]; exact ⟨fun h' => absurd h' (hirr j), fun h' => by arith⟩
      · rw [h q hq hqj]; exact ⟨fun h' => by arith, fun h' => by arith⟩
    · right
      intro q hq
      by_cases hqj : q = j
      · rw [hqj]; exact ⟨fun h' => absurd h' (hirr j), fun h' => by arith⟩
      · rw [h q hq hqj]; exact ⟨fun h' => by arith, fun h' => by arith⟩

/-- Conversely every graph of one of the four classes is a flip. -/
theorem flip_of_cls {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (_hG : G ∈ graphs S) (hc : Cls S i j φi φj G) (_hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hφ : ¬ φi j)
    (hmi : MonoP S i (fun q => φi q ∨ q = j)) (hmj : MonoP S j (fun q => φj q ∨ q = i)) :
    IsFlip S i j G := by
  refine ⟨hc.cons, fun h => hφ ((hc.rowi j hj).mp (Or.inl h)), ?_⟩
  intro p hp
  by_cases hpi : p = i
  · rw [hpi]
    refine hmi.congr ?_
    intro q hq _
    rw [adj_insert, hc.rowi q hq]
    constructor
    · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
      · omega
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  by_cases hpj : p = j
  · rw [hpj]
    refine hmj.congr ?_
    intro q hq _
    rw [adj_insert, hc.rowj q hq]
    constructor
    · rintro (h | ⟨h, _⟩ | ⟨_, h⟩)
      · exact Or.inl h
      · omega
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
  refine (hc.cons p hp).congr ?_
  intro q _ _
  rw [adj_insert]
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h hpi
    · exact absurd h hpj
  · exact fun h => Or.inl h

theorem mono_iD' (S : Finset ℕ) (i j : ℕ) : MonoP S i (fun q => iD i j q ∨ q = j) :=
  Or.inl (fun x _ y _ hxi _ hxy hy => by arith)

theorem mono_iU' (S : Finset ℕ) (i j : ℕ) : MonoP S i (fun q => iU j q ∨ q = j) :=
  Or.inr (fun x _ y _ _ _ hxy hx => by arith)

theorem mono_jD' (S : Finset ℕ) (i j : ℕ) : MonoP S j (fun q => jD i q ∨ q = i) :=
  Or.inl (fun x _ y _ _ _ hxy hy => by arith)

theorem mono_jU' (S : Finset ℕ) (i j : ℕ) : MonoP S j (fun q => jU i j q ∨ q = i) :=
  Or.inr (fun x _ y _ _ hyj hxy hx => by arith)

/-- The flips at `ij` split into the four classes. -/
theorem card_flipSet {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (h3 : 3 ≤ S.card) :
    (flipSet S i j).card
      = ((clsSet S i j (iD i j) (jD i)).card + (clsSet S i j (iD i j) (jU i j)).card)
        + ((clsSet S i j (iU j) (jD i)).card + (clsSet S i j (iU j) (jU i j)).card) := by
  -- a third vertex
  obtain ⟨r, hr, hri, hrj⟩ : ∃ r ∈ S, r ≠ i ∧ r ≠ j := by
    have hcard : 0 < ((S.erase i).erase j).card := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨by omega, hj⟩), card_erase_of_mem hi]
      omega
    obtain ⟨r, hr⟩ := card_pos.mp hcard
    exact ⟨r, (mem_erase.mp (mem_erase.mp hr).2).2, (mem_erase.mp (mem_erase.mp hr).2).1,
      (mem_erase.mp hr).1⟩
  have exi : ∀ G : Graph, (∀ q ∈ S, (adj G i q ↔ iU j q)) → (∀ q ∈ S, (adj G i q ↔ iD i j q)) →
      False := by
    intro G hU hD
    have := (hD r hr).symm.trans (hU r hr)
    arith
  have exj : ∀ G : Graph, (∀ q ∈ S, (adj G j q ↔ jU i j q)) → (∀ q ∈ S, (adj G j q ↔ jD i q)) →
      False := by
    intro G hU hD
    have := (hD r hr).symm.trans (hU r hr)
    arith
  have s1 := card_split (S := S) (IsFlip S i j)
    (fun G => ∀ q ∈ S, (adj G i q ↔ iD i j q)) (fun G => ∀ q ∈ S, (adj G i q ↔ iU j q))
    (fun G hG hf => ⟨fun hU hD => exi G hU hD,
      fun hnD => (rows_of_flip hG hi hj hij hf).1.resolve_left hnD⟩)
  have s2 := card_split (S := S)
    (fun G => IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iD i j q))
    (fun G => ∀ q ∈ S, (adj G j q ↔ jD i q)) (fun G => ∀ q ∈ S, (adj G j q ↔ jU i j q))
    (fun G hG hf => ⟨fun hU hD => exj G hU hD,
      fun hnD => (rows_of_flip hG hi hj hij hf.1).2.resolve_left hnD⟩)
  have s3 := card_split (S := S)
    (fun G => IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iU j q))
    (fun G => ∀ q ∈ S, (adj G j q ↔ jD i q)) (fun G => ∀ q ∈ S, (adj G j q ↔ jU i j q))
    (fun G hG hf => ⟨fun hU hD => exj G hU hD,
      fun hnD => (rows_of_flip hG hi hj hij hf.1).2.resolve_left hnD⟩)
  have e1 : (sel S fun G => (IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iD i j q)) ∧
      ∀ q ∈ S, (adj G j q ↔ jD i q)) = clsSet S i j (iD i j) (jD i) := by
    apply sel_congr
    intro G hG
    constructor
    · rintro ⟨⟨hf, h1⟩, h2⟩; exact ⟨hf.1, h1, h2⟩
    · intro hc
      exact ⟨⟨flip_of_cls hG hc hi hj hij (by arith) (mono_iD' S i j) (mono_jD' S i j),
        hc.rowi⟩, hc.rowj⟩
  have e2 : (sel S fun G => (IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iD i j q)) ∧
      ∀ q ∈ S, (adj G j q ↔ jU i j q)) = clsSet S i j (iD i j) (jU i j) := by
    apply sel_congr
    intro G hG
    constructor
    · rintro ⟨⟨hf, h1⟩, h2⟩; exact ⟨hf.1, h1, h2⟩
    · intro hc
      exact ⟨⟨flip_of_cls hG hc hi hj hij (by arith) (mono_iD' S i j) (mono_jU' S i j),
        hc.rowi⟩, hc.rowj⟩
  have e3 : (sel S fun G => (IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iU j q)) ∧
      ∀ q ∈ S, (adj G j q ↔ jD i q)) = clsSet S i j (iU j) (jD i) := by
    apply sel_congr
    intro G hG
    constructor
    · rintro ⟨⟨hf, h1⟩, h2⟩; exact ⟨hf.1, h1, h2⟩
    · intro hc
      exact ⟨⟨flip_of_cls hG hc hi hj hij (by arith) (mono_iU' S i j) (mono_jD' S i j),
        hc.rowi⟩, hc.rowj⟩
  have e4 : (sel S fun G => (IsFlip S i j G ∧ ∀ q ∈ S, (adj G i q ↔ iU j q)) ∧
      ∀ q ∈ S, (adj G j q ↔ jU i j q)) = clsSet S i j (iU j) (jU i j) := by
    apply sel_congr
    intro G hG
    constructor
    · rintro ⟨⟨hf, h1⟩, h2⟩; exact ⟨hf.1, h1, h2⟩
    · intro hc
      exact ⟨⟨flip_of_cls hG hc hi hj hij (by arith) (mono_iU' S i j) (mono_jU' S i j),
        hc.rowi⟩, hc.rowj⟩
  unfold flipSet
  rw [s1, s2, s3, e1, e2, e3, e4]

end

end ZonoFlips
