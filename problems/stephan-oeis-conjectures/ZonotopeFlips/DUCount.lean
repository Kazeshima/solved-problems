import ZonotopeFlips.DU

/-!
# Counting the class `DU`

`card_DU`: the class has `choose (|A| + |B| + |C|) |B|` elements.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

theorem not_adj_empty {x y : ℕ} : ¬ adj (∅ : Graph) x y := by
  unfold adj; simp

/-- With no vertex besides `i` and `j` a class consists of the empty graph alone. -/
theorem card_cls_base {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} (hij : i < j)
    (hS : ∀ q ∈ S, q = i ∨ q = j)
    (h1 : ¬ φi i) (h2 : ¬ φi j) (h3 : ¬ φj i) (h4 : ¬ φj j) :
    (clsSet S i j φi φj).card = 1 := by
  rw [card_eq_one]
  refine ⟨∅, ?_⟩
  ext G
  rw [mem_clsSet, mem_singleton]
  constructor
  · rintro ⟨hG, hc⟩
    apply graph_ext hG (mem_graphs.mpr (empty_subset _))
    intro x hx y hy hxy
    have hx' := hS x hx
    have hy' := hS y hy
    have hxi : x = i := by omega
    have hyj : y = j := by omega
    rw [hxi, hyj]
    constructor
    · intro h; exact absurd ((hc.rowi j (hyj ▸ hy)).mp h) h2
    · intro h; exact absurd h not_adj_empty
  · intro hG
    rw [hG]
    refine ⟨mem_graphs.mpr (empty_subset _), ⟨?_, ?_, ?_⟩⟩
    · intro p _
      left
      intro x _ y _ _ _ _ h
      exact absurd h not_adj_empty
    · intro q hq
      constructor
      · intro h; exact absurd h not_adj_empty
      · intro h
        rcases hS q hq with e | e
        · exact absurd (e ▸ h) h1
        · exact absurd (e ▸ h) h2
    · intro q hq
      constructor
      · intro h; exact absurd h not_adj_empty
      · intro h
        rcases hS q hq with e | e
        · exact absurd (e ▸ h) h3
        · exact absurd (e ▸ h) h4

theorem pascal_ab (α β γ : ℕ) :
    Nat.choose (α + (β + 1) + γ) (β + 1) + Nat.choose (α + 1 + β + γ) β
      = Nat.choose (α + 1 + (β + 1) + γ) (β + 1) := by
  have e1 : α + (β + 1) + γ = (α + β + γ) + 1 := by omega
  have e2 : α + 1 + β + γ = (α + β + γ) + 1 := by omega
  have e3 : α + 1 + (β + 1) + γ = ((α + β + γ) + 1) + 1 := by omega
  rw [e1, e2, e3, Nat.choose_succ_succ' ((α + β + γ) + 1) β]
  exact Nat.add_comm _ _

theorem pascal_cb (α β γ : ℕ) :
    Nat.choose (α + (β + 1) + γ) (β + 1) + Nat.choose (α + β + (γ + 1)) β
      = Nat.choose (α + (β + 1) + (γ + 1)) (β + 1) := by
  have e1 : α + (β + 1) + γ = (α + β + γ) + 1 := by omega
  have e2 : α + β + (γ + 1) = (α + β + γ) + 1 := by omega
  have e3 : α + (β + 1) + (γ + 1) = ((α + β + γ) + 1) + 1 := by omega
  rw [e1, e2, e3, Nat.choose_succ_succ' ((α + β + γ) + 1) β]
  exact Nat.add_comm _ _

/-- The class `DU` has `choose (|A| + |B| + |C|) |B|` elements. -/
theorem card_DU : ∀ (m : ℕ) (S : Finset ℕ) (i j : ℕ), S.card = m → i ∈ S → j ∈ S → i < j →
    (clsSet S i j (iD i j) (jU i j)).card
      = Nat.choose (nA S i + nB S i j + nC S j) (nB S i j) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S i j hS hi hj hij
  have hmpos : 0 < m := by rw [← hS]; exact card_pos.mpr ⟨i, hi⟩
  by_cases hA : (S.filter fun q => q < i).Nonempty
  · obtain ⟨a, ha, hai, hamax⟩ := exists_max_of_nonempty hA
    have iha := ih (m - 1) (by omega) (S.erase a) i j (by rw [card_erase_of_mem ha]; omega)
      (mem_erase.mpr ⟨by omega, hi⟩) (mem_erase.mpr ⟨by omega, hj⟩) hij
    have eA : nA (S.erase a) i + 1 = nA S i := card_filter_erase_pos _ ha hai
    have eB : nB (S.erase a) i j = nB S i j := card_filter_erase_neg _ (by omega)
    have eC : nC (S.erase a) j = nC S j := card_filter_erase_neg _ (by omega)
    by_cases hB : (S.filter fun q => i < q ∧ q < j).Nonempty
    · obtain ⟨b, hb, ⟨hib, hbj⟩, hbm⟩ := exists_max_of_nonempty hB
      have hbmax : ∀ q ∈ S, q < j → q ≤ b := fun q hq hqj => by
        by_cases h : i < q
        · exact hbm q hq ⟨h, hqj⟩
        · omega
      have ihb := ih (m - 1) (by omega) (S.erase b) i j (by rw [card_erase_of_mem hb]; omega)
        (mem_erase.mpr ⟨by omega, hi⟩) (mem_erase.mpr ⟨by omega, hj⟩) hij
      have fA : nA (S.erase b) i = nA S i := card_filter_erase_neg _ (by omega)
      have fB : nB (S.erase b) i j + 1 = nB S i j := card_filter_erase_pos _ hb ⟨hib, hbj⟩
      have fC : nC (S.erase b) j = nC S j := card_filter_erase_neg _ (by omega)
      have split := card_split (S := S) (Cls S i j (iD i j) (jU i j))
        (fun G => ∀ q ∈ S, i < q → q < j → adj G a q)
        (fun G => (∀ q ∈ S, q < i → ¬ adj G b q) ∧ (∀ q ∈ S, j < q → adj G b q))
        (fun G _ hc => DU_dich_ab hc hi hj hij ha hai hamax hb hib hbj hbmax)
      rw [DU_del_a hi hj hij ha hai hamax, DU_del_b hi hj hij hb hib hbj hbmax, iha, ihb] at split
      show (sel S (Cls S i j (iD i j) (jU i j))).card = _
      rw [split, eB, eC, fA, fC, ← eA, ← fB]
      exact pascal_ab _ _ _
    · have hB0 : nB S i j = 0 := card_zero_of_not_nonempty hB
      have hnoB := forall_not_of_not_nonempty hB
      have e := card_of_forall (S := S) (Cls S i j (iD i j) (jU i j))
        (fun G => ∀ q ∈ S, i < q → q < j → adj G a q)
        (fun G _ _ q hq h1 h2 => absurd ⟨h1, h2⟩ (hnoB q hq))
      show (sel S (Cls S i j (iD i j) (jU i j))).card = _
      rw [e, DU_del_a hi hj hij ha hai hamax, iha, eB, hB0, Nat.choose_zero_right,
        Nat.choose_zero_right]
  · have hA0 : nA S i = 0 := card_zero_of_not_nonempty hA
    have hnoA := forall_not_of_not_nonempty hA
    by_cases hC : (S.filter fun q => j < q).Nonempty
    · obtain ⟨c, hc', hjc, hcmin⟩ := exists_min_of_nonempty hC
      have ihc := ih (m - 1) (by omega) (S.erase c) i j (by rw [card_erase_of_mem hc']; omega)
        (mem_erase.mpr ⟨by omega, hi⟩) (mem_erase.mpr ⟨by omega, hj⟩) hij
      have gA : nA (S.erase c) i = nA S i := card_filter_erase_neg _ (by omega)
      have gB : nB (S.erase c) i j = nB S i j := card_filter_erase_neg _ (by omega)
      have gC : nC (S.erase c) j + 1 = nC S j := card_filter_erase_pos _ hc' hjc
      by_cases hB : (S.filter fun q => i < q ∧ q < j).Nonempty
      · obtain ⟨b, hb, ⟨hib, hbj⟩, hbm⟩ := exists_min_of_nonempty hB
        have hbmin : ∀ q ∈ S, i < q → b ≤ q := fun q hq hiq => by
          by_cases h : q < j
          · exact hbm q hq ⟨hiq, h⟩
          · omega
        have ihb := ih (m - 1) (by omega) (S.erase b) i j (by rw [card_erase_of_mem hb]; omega)
          (mem_erase.mpr ⟨by omega, hi⟩) (mem_erase.mpr ⟨by omega, hj⟩) hij
        have fA : nA (S.erase b) i = nA S i := card_filter_erase_neg _ (by omega)
        have fB : nB (S.erase b) i j + 1 = nB S i j := card_filter_erase_pos _ hb ⟨hib, hbj⟩
        have fC : nC (S.erase b) j = nC S j := card_filter_erase_neg _ (by omega)
        have split := card_split (S := S) (Cls S i j (iD i j) (jU i j))
          (fun G => ∀ q ∈ S, i < q → q < j → adj G c q)
          (fun G => (∀ q ∈ S, j < q → ¬ adj G b q) ∧ (∀ q ∈ S, q < i → adj G b q))
          (fun G _ hc => DU_dich_cd hc hi hj hij hc' hjc hcmin hb hib hbj hbmin)
        rw [DU_del_c hi hj hij hc' hjc hcmin, DU_del_d hi hj hij hb hib hbj hbmin, ihc, ihb]
          at split
        show (sel S (Cls S i j (iD i j) (jU i j))).card = _
        rw [split, gA, gB, fA, fC, ← gC, ← fB]
        exact pascal_cb _ _ _
      · have hB0 : nB S i j = 0 := card_zero_of_not_nonempty hB
        have hnoB := forall_not_of_not_nonempty hB
        have e := card_of_forall (S := S) (Cls S i j (iD i j) (jU i j))
          (fun G => ∀ q ∈ S, i < q → q < j → adj G c q)
          (fun G _ _ q hq h1 h2 => absurd ⟨h1, h2⟩ (hnoB q hq))
        show (sel S (Cls S i j (iD i j) (jU i j))).card = _
        rw [e, DU_del_c hi hj hij hc' hjc hcmin, ihc, gB, hB0, Nat.choose_zero_right,
          Nat.choose_zero_right]
    · have hC0 : nC S j = 0 := card_zero_of_not_nonempty hC
      have hnoC := forall_not_of_not_nonempty hC
      by_cases hB : (S.filter fun q => i < q ∧ q < j).Nonempty
      · obtain ⟨b, hb, ⟨hib, hbj⟩, hbm⟩ := exists_max_of_nonempty hB
        have hbmax : ∀ q ∈ S, q < j → q ≤ b := fun q hq hqj => by
          by_cases h : i < q
          · exact hbm q hq ⟨h, hqj⟩
          · omega
        have ihb := ih (m - 1) (by omega) (S.erase b) i j (by rw [card_erase_of_mem hb]; omega)
          (mem_erase.mpr ⟨by omega, hi⟩) (mem_erase.mpr ⟨by omega, hj⟩) hij
        have fA : nA (S.erase b) i = nA S i := card_filter_erase_neg _ (by omega)
        have fB : nB (S.erase b) i j + 1 = nB S i j := card_filter_erase_pos _ hb ⟨hib, hbj⟩
        have fC : nC (S.erase b) j = nC S j := card_filter_erase_neg _ (by omega)
        have e := card_of_forall (S := S) (Cls S i j (iD i j) (jU i j))
          (fun G => (∀ q ∈ S, q < i → ¬ adj G b q) ∧ (∀ q ∈ S, j < q → adj G b q))
          (fun G _ _ => ⟨fun q hq h => absurd h (hnoA q hq), fun q hq h => absurd h (hnoC q hq)⟩)
        show (sel S (Cls S i j (iD i j) (jU i j))).card = _
        rw [e, DU_del_b hi hj hij hb hib hbj hbmax, ihb, fA, fC, hA0, hC0, ← fB]
        simp
      · have hB0 : nB S i j = 0 := card_zero_of_not_nonempty hB
        have hnoB := forall_not_of_not_nonempty hB
        rw [hA0, hB0, hC0]
        refine card_cls_base hij ?_ (by arith) (by arith) (by arith) (by arith)
        intro q hq
        have h1 := hnoA q hq
        have h2 := hnoB q hq
        have h3 := hnoC q hq
        omega

end

end ZonoFlips
