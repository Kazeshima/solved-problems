import ZonotopeFlips.DD

/-!
# Counting the class `DD`

`card_DD`: the class has `2 ^ ((|B| - 1) + (|A| + |C| - 1))` elements (truncated subtraction).
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

theorem pow_sum_eq {a b c : ℕ} (h1 : a = b) (h2 : c = a + 1) : 2 ^ a + 2 ^ b = 2 ^ c := by
  subst h1; subst h2; rw [pow_succ]; ring

theorem pow_eq_of_eq {a c : ℕ} (h : a = c) : 2 ^ a = 2 ^ c := by rw [h]

/-- The class `DD` has `2 ^ ((|B| - 1) + (|A| + |C| - 1))` elements. -/
theorem card_DD : ∀ (m : ℕ) (S : Finset ℕ) (i j : ℕ), S.card = m → i ∈ S → j ∈ S → i < j →
    (clsSet S i j (iD i j) (jD i)).card
      = 2 ^ ((nB S i j - 1) + (nA S i + nC S j - 1)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S i j hS hi hj hij
  have hmpos : 0 < m := by rw [← hS]; exact card_pos.mpr ⟨i, hi⟩
  -- induction hypothesis for the deletion of one vertex
  have IH : ∀ w ∈ S, w ≠ i → w ≠ j →
      (clsSet (S.erase w) i j (iD i j) (jD i)).card
        = 2 ^ ((nB (S.erase w) i j - 1) + (nA (S.erase w) i + nC (S.erase w) j - 1)) :=
    fun w hw hwi hwj => ih (m - 1) (by omega) (S.erase w) i j
      (by rw [card_erase_of_mem hw]; omega)
      (mem_erase.mpr ⟨Ne.symm hwi, hi⟩) (mem_erase.mpr ⟨Ne.symm hwj, hj⟩) hij
  show (sel S (Cls S i j (iD i j) (jD i))).card = _
  by_cases hB : (S.filter fun q => i < q ∧ q < j).Nonempty
  · obtain ⟨b2, hb2, ⟨hib2, hb2j⟩, hbm2⟩ := exists_max_of_nonempty hB
    have hbmax : ∀ q ∈ S, q < j → q ≤ b2 := fun q hq hqj => by
      by_cases h : i < q
      · exact hbm2 q hq ⟨h, hqj⟩
      · omega
    have ih2 := IH b2 hb2 (by omega) (by omega)
    have fA2 : nA (S.erase b2) i = nA S i := card_filter_erase_neg _ (by omega)
    have fB2 : nB (S.erase b2) i j + 1 = nB S i j := card_filter_erase_pos _ hb2 ⟨hib2, hb2j⟩
    have fC2 : nC (S.erase b2) j = nC S j := card_filter_erase_neg _ (by omega)
    by_cases hother : ∃ q ∈ S, i < q ∧ q < j ∧ q ≠ b2
    · obtain ⟨b1, hb1, ⟨hib1, hb1j⟩, hbm1⟩ := exists_min_of_nonempty hB
      have hbmin : ∀ q ∈ S, i < q → b1 ≤ q := fun q hq hiq => by
        by_cases h : q < j
        · exact hbm1 q hq ⟨hiq, h⟩
        · omega
      obtain ⟨q0, hq0, h01, h02, h03⟩ := hother
      have hne : b1 ≠ b2 := by
        have := hbm1 q0 hq0 ⟨h01, h02⟩
        have := hbmax q0 hq0 h02
        omega
      have ih1 := IH b1 hb1 (by omega) (by omega)
      have fA1 : nA (S.erase b1) i = nA S i := card_filter_erase_neg _ (by omega)
      have fB1 : nB (S.erase b1) i j + 1 = nB S i j := card_filter_erase_pos _ hb1 ⟨hib1, hb1j⟩
      have fC1 : nC (S.erase b1) j = nC S j := card_filter_erase_neg _ (by omega)
      have hpos : 1 ≤ nB (S.erase b2) i j :=
        card_pos.mpr ⟨q0, mem_filter.mpr ⟨mem_erase.mpr ⟨h03, hq0⟩, h01, h02⟩⟩
      have split := card_split (S := S) (Cls S i j (iD i j) (jD i))
        (fun G => ∀ q ∈ S, i < q → q < j → q ≠ b1 → adj G b1 q)
        (fun G => ∀ q ∈ S, i < q → q < j → q ≠ b2 → ¬ adj G b2 q)
        (fun G _ hc => DD_dich_b hc hi hj hij hb1 hib1 hb1j hbmin hb2 hib2 hb2j hbmax hne)
      rw [DD_del_bmin hi hj hij hb1 hib1 hb1j hbmin, DD_del_bmax hi hj hij hb2 hib2 hb2j hbmax,
        ih1, ih2] at split
      rw [split]
      exact pow_sum_eq (by omega) (by omega)
    · have hother' : ∀ q ∈ S, i < q → q < j → q = b2 := by
        intro q hq h1 h2
        by_contra h3
        exact hother ⟨q, hq, h1, h2, h3⟩
      have e := card_of_forall (S := S) (Cls S i j (iD i j) (jD i))
        (fun G => ∀ q ∈ S, i < q → q < j → q ≠ b2 → ¬ adj G b2 q)
        (fun G _ _ q hq h1 h2 h3 => absurd (hother' q hq h1 h2) h3)
      have h0 : nB (S.erase b2) i j = 0 := by
        unfold nB
        rw [card_eq_zero, filter_eq_empty_iff]
        intro q hq hh
        exact (mem_erase.mp hq).1 (hother' q (mem_erase.mp hq).2 hh.1 hh.2)
      rw [e, DD_del_bmax hi hj hij hb2 hib2 hb2j hbmax, ih2]
      exact pow_eq_of_eq (by omega)
  · have hB0 : nB S i j = 0 := card_zero_of_not_nonempty hB
    have hnoB := forall_not_of_not_nonempty hB
    by_cases hA : (S.filter fun q => q < i).Nonempty
    · obtain ⟨a2, ha2, ha2i, hamax⟩ := exists_max_of_nonempty hA
      have iha2 := IH a2 ha2 (by omega) (by omega)
      have eA2 : nA (S.erase a2) i + 1 = nA S i := card_filter_erase_pos _ ha2 ha2i
      have eB2 : nB (S.erase a2) i j = nB S i j := card_filter_erase_neg _ (by omega)
      have eC2 : nC (S.erase a2) j = nC S j := card_filter_erase_neg _ (by omega)
      by_cases hC : (S.filter fun q => j < q).Nonempty
      · obtain ⟨c1, hc1, hjc1, hcmin⟩ := exists_min_of_nonempty hC
        have ihc := IH c1 hc1 (by omega) (by omega)
        have gA : nA (S.erase c1) i = nA S i := card_filter_erase_neg _ (by omega)
        have gB : nB (S.erase c1) i j = nB S i j := card_filter_erase_neg _ (by omega)
        have gC : nC (S.erase c1) j + 1 = nC S j := card_filter_erase_pos _ hc1 hjc1
        have split := card_split (S := S) (Cls S i j (iD i j) (jD i))
          (fun G => (∀ q ∈ S, q < i → adj G c1 q) ∧ (∀ q ∈ S, j < q → q ≠ c1 → ¬ adj G c1 q))
          (fun G => (∀ q ∈ S, q < i → q ≠ a2 → adj G a2 q) ∧ (∀ q ∈ S, j < q → ¬ adj G a2 q))
          (fun G _ hc => DD_dich_ac hc hi hj hij ha2 ha2i hamax hc1 hjc1 hcmin)
        rw [DD_del_c hi hj hij hc1 hjc1 hcmin, DD_del_amax hi hj hij ha2 ha2i hamax, ihc, iha2]
          at split
        rw [split]
        exact pow_sum_eq (by omega) (by omega)
      · have hC0 : nC S j = 0 := card_zero_of_not_nonempty hC
        have hnoC := forall_not_of_not_nonempty hC
        have hmaxj : ∀ q ∈ S, q ≤ j := fun q hq => by have := hnoC q hq; omega
        by_cases hother : ∃ q ∈ S, q < i ∧ q ≠ a2
        · obtain ⟨a1, ha1, ha1i, hamin'⟩ := exists_min_of_nonempty hA
          have hamin : ∀ q ∈ S, a1 ≤ q := fun q hq => by
            by_cases h : q < i
            · exact hamin' q hq h
            · omega
          obtain ⟨q0, hq0, h01, h02⟩ := hother
          have hne : a1 ≠ a2 := by
            have := hamin q0 hq0
            have := hamax q0 hq0 h01
            omega
          have ih1 := IH a1 ha1 (by omega) (by omega)
          have eA1 : nA (S.erase a1) i + 1 = nA S i := card_filter_erase_pos _ ha1 ha1i
          have eB1 : nB (S.erase a1) i j = nB S i j := card_filter_erase_neg _ (by omega)
          have eC1 : nC (S.erase a1) j = nC S j := card_filter_erase_neg _ (by omega)
          have hpos : 1 ≤ nA (S.erase a2) i :=
            card_pos.mpr ⟨q0, mem_filter.mpr ⟨mem_erase.mpr ⟨h02, hq0⟩, h01⟩⟩
          have split := card_split (S := S) (Cls S i j (iD i j) (jD i))
            (fun G => (∀ q ∈ S, q < i → q ≠ a2 → adj G a2 q) ∧ (∀ q ∈ S, j < q → ¬ adj G a2 q))
            (fun G => ∀ q ∈ S, q < i → q ≠ a1 → ¬ adj G a1 q)
            (fun G _ hc => DD_dich_a hc hi hj hij ha1 ha1i hamin ha2 ha2i hamax hmaxj hne)
          rw [DD_del_amax hi hj hij ha2 ha2i hamax,
            DD_del_amin hi hj hij ha1 ha1i hamin hnoB hmaxj, iha2, ih1] at split
          rw [split]
          exact pow_sum_eq (by omega) (by omega)
        · have hother' : ∀ q ∈ S, q < i → q = a2 := by
            intro q hq h1
            by_contra h3
            exact hother ⟨q, hq, h1, h3⟩
          have e := card_of_forall (S := S) (Cls S i j (iD i j) (jD i))
            (fun G => (∀ q ∈ S, q < i → q ≠ a2 → adj G a2 q) ∧ (∀ q ∈ S, j < q → ¬ adj G a2 q))
            (fun G _ _ => ⟨fun q hq h1 h3 => absurd (hother' q hq h1) h3,
              fun q hq h => absurd h (hnoC q hq)⟩)
          have h0 : nA (S.erase a2) i = 0 := by
            unfold nA
            rw [card_eq_zero, filter_eq_empty_iff]
            intro q hq hh
            exact (mem_erase.mp hq).1 (hother' q (mem_erase.mp hq).2 hh)
          rw [e, DD_del_amax hi hj hij ha2 ha2i hamax, iha2]
          exact pow_eq_of_eq (by omega)
    · have hA0 : nA S i = 0 := card_zero_of_not_nonempty hA
      have hnoA := forall_not_of_not_nonempty hA
      have hmini : ∀ q ∈ S, i ≤ q := fun q hq => by have := hnoA q hq; omega
      by_cases hC : (S.filter fun q => j < q).Nonempty
      · obtain ⟨c1, hc1, hjc1, hcmin⟩ := exists_min_of_nonempty hC
        have ihc1 := IH c1 hc1 (by omega) (by omega)
        have gA : nA (S.erase c1) i = nA S i := card_filter_erase_neg _ (by omega)
        have gB : nB (S.erase c1) i j = nB S i j := card_filter_erase_neg _ (by omega)
        have gC : nC (S.erase c1) j + 1 = nC S j := card_filter_erase_pos _ hc1 hjc1
        by_cases hother : ∃ q ∈ S, j < q ∧ q ≠ c1
        · obtain ⟨c2, hc2, hjc2, hcmax'⟩ := exists_max_of_nonempty hC
          have hcmax : ∀ q ∈ S, q ≤ c2 := fun q hq => by
            by_cases h : j < q
            · exact hcmax' q hq h
            · omega
          obtain ⟨q0, hq0, h01, h02⟩ := hother
          have hne : c1 ≠ c2 := by
            have := hcmin q0 hq0 h01
            have := hcmax q0 hq0
            omega
          have ihc2 := IH c2 hc2 (by omega) (by omega)
          have kA : nA (S.erase c2) i = nA S i := card_filter_erase_neg _ (by omega)
          have kB : nB (S.erase c2) i j = nB S i j := card_filter_erase_neg _ (by omega)
          have kC : nC (S.erase c2) j + 1 = nC S j := card_filter_erase_pos _ hc2 hjc2
          have hpos : 1 ≤ nC (S.erase c1) j :=
            card_pos.mpr ⟨q0, mem_filter.mpr ⟨mem_erase.mpr ⟨h02, hq0⟩, h01⟩⟩
          have split := card_split (S := S) (Cls S i j (iD i j) (jD i))
            (fun G => ∀ q ∈ S, j < q → q ≠ c2 → adj G c2 q)
            (fun G => (∀ q ∈ S, q < i → adj G c1 q) ∧ (∀ q ∈ S, j < q → q ≠ c1 → ¬ adj G c1 q))
            (fun G _ hc => DD_dich_c hc hi hj hij hc1 hjc1 hcmin hc2 hjc2 hcmax hmini hne)
          rw [DD_del_cmax hi hj hij hc2 hjc2 hcmax hnoB hmini,
            DD_del_c hi hj hij hc1 hjc1 hcmin, ihc2, ihc1] at split
          rw [split]
          exact pow_sum_eq (by omega) (by omega)
        · have hother' : ∀ q ∈ S, j < q → q = c1 := by
            intro q hq h1
            by_contra h3
            exact hother ⟨q, hq, h1, h3⟩
          have e := card_of_forall (S := S) (Cls S i j (iD i j) (jD i))
            (fun G => (∀ q ∈ S, q < i → adj G c1 q) ∧ (∀ q ∈ S, j < q → q ≠ c1 → ¬ adj G c1 q))
            (fun G _ _ => ⟨fun q hq h => absurd h (hnoA q hq),
              fun q hq h1 h3 => absurd (hother' q hq h1) h3⟩)
          have h0 : nC (S.erase c1) j = 0 := by
            unfold nC
            rw [card_eq_zero, filter_eq_empty_iff]
            intro q hq hh
            exact (mem_erase.mp hq).1 (hother' q (mem_erase.mp hq).2 hh)
          rw [e, DD_del_c hi hj hij hc1 hjc1 hcmin, ihc1]
          exact pow_eq_of_eq (by omega)
      · have hC0 : nC S j = 0 := card_zero_of_not_nonempty hC
        have hnoC := forall_not_of_not_nonempty hC
        rw [hA0, hB0, hC0]
        show (clsSet S i j (iD i j) (jD i)).card = _
        rw [card_cls_base hij ?_ (by arith) (by arith) (by arith) (by arith)]
        · rfl
        · intro q hq
          have h1 := hnoA q hq
          have h2 := hnoB q hq
          have h3 := hnoC q hq
          omega

end

end ZonoFlips
