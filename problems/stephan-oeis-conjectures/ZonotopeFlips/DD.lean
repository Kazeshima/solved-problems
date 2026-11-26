import ZonotopeFlips.DUCount

/-!
# The class `DD`: `N(i) = {q < j} \ {i}` and `N(j) = {q < i}`

Deletion steps and dichotomies for the class in which both marked rows are initial segments.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

/-! ### Deleting a vertex of `B` -/

/-- Deleting the smallest vertex of `B` when it is joined to the rest of `B`. -/
theorem DD_del_bmin {S : Finset ℕ} {i j b : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmin : ∀ q ∈ S, i < q → b ≤ q) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ∀ q ∈ S, i < q → q < j → q ≠ b → adj G b q).card
      = (clsSet (S.erase b) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => q < j ∧ q ≠ b) _ hi hj hb (by omega) (by omega)
  · show (i < j ∧ i ≠ b) ↔ iD i j b
    arith
  · show (j < j ∧ j ≠ b) ↔ jD i b
    arith
  · intro G hG hc hcond q hq hqb
    have h1 : adj G b i := (hc.adj_i hb).mpr (by arith)
    have h2 : ¬ adj G b j := fun h => by have := (hc.adj_j hb).mp h; arith
    show adj G b q ↔ (q < j ∧ q ≠ b)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun h => absurd h h2, fun h => by omega⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · have := hc.no010 hb hq hi hj hqb (by omega) (by omega) hlt hij h1
      exact ⟨fun _ => by omega, fun _ => this.resolve_right h2⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega, fun _ => hcond q hq (by omega) hlt2 hqb⟩
      · refine ⟨fun h => ?_, fun h => by omega⟩
        exact absurd (hc.no101 hb hi hj hq (by omega) (by omega) hqb hij (by omega) h1 h) h2
  · intro H hH hc
    constructor
    · apply cons_ins_clone_i hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jD S i j)
      · exact Or.inl (fun x _ y _ hxb _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hbmin q hq
        omega
      · intro p _ h1 h2 h3
        show (p < j ∧ p ≠ b) ↔ iD i j p
        arith
      · show (i < j ∧ i ≠ b) ↔ iD i j b
        arith
      · show (j < j ∧ j ≠ b) ↔ jD i b
        arith
    · intro q hq h1 h2 h3
      exact (adj_ins_self hH hq h3).mpr ⟨h2, h3⟩

/-- Deleting the largest vertex of `B` when it has no neighbour in `B`. -/
theorem DD_del_bmax {S : Finset ℕ} {i j b : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmax : ∀ q ∈ S, q < j → q ≤ b) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ∀ q ∈ S, i < q → q < j → q ≠ b → ¬ adj G b q).card
      = (clsSet (S.erase b) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => q ≤ i) _ hi hj hb (by omega) (by omega)
  · show (i ≤ i) ↔ iD i j b
    arith
  · show (j ≤ i) ↔ jD i b
    arith
  · intro G hG hc hcond q hq hqb
    have h1 : adj G b i := (hc.adj_i hb).mpr (by arith)
    have h2 : ¬ adj G b j := fun h => by have := (hc.adj_j hb).mp h; arith
    show adj G b q ↔ q ≤ i
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun h => absurd h h2, fun h => by omega⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · have := hc.no010 hb hq hi hj hqb (by omega) (by omega) hlt hij h1
      exact ⟨fun _ => by omega, fun _ => this.resolve_right h2⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun h => absurd h (hcond q hq (by omega) hlt2 hqb), fun h => by omega⟩
      · refine ⟨fun h => ?_, fun h => by omega⟩
        exact absurd (hc.no101 hb hi hj hq (by omega) (by omega) hqb hij (by omega) h1 h) h2
  · intro H hH hc
    constructor
    · apply cons_ins_clone_j hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jD S i j)
      · exact Or.inl (fun x _ y _ _ _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hbmax q hq
        omega
      · intro p _ h1 h2 h3
        show (p ≤ i) ↔ jD i p
        arith
      · show (i ≤ i) ↔ iD i j b
        arith
      · show (j ≤ i) ↔ jD i b
        arith
    · intro q hq h1 h2 h3 h
      have := (adj_ins_self hH hq h3).mp h
      omega

theorem DD_dich_b {S : Finset ℕ} {G : Graph} {i j b1 b2 : ℕ}
    (hc : Cls S i j (iD i j) (jD i) G) (_hi : i ∈ S) (hj : j ∈ S) (_hij : i < j)
    (hb1 : b1 ∈ S) (hib1 : i < b1) (hb1j : b1 < j) (hbmin : ∀ q ∈ S, i < q → b1 ≤ q)
    (hb2 : b2 ∈ S) (hib2 : i < b2) (hb2j : b2 < j) (hbmax : ∀ q ∈ S, q < j → q ≤ b2)
    (hne : b1 ≠ b2) :
    (∀ q ∈ S, i < q → q < j → q ≠ b2 → ¬ adj G b2 q) ↔
      ¬ (∀ q ∈ S, i < q → q < j → q ≠ b1 → adj G b1 q) := by
  have h1j : ¬ adj G b1 j := fun h => by have := (hc.adj_j hb1).mp h; arith
  have h2j : ¬ adj G b2 j := fun h => by have := (hc.adj_j hb2).mp h; arith
  have hlt12 : b1 < b2 := by have := hbmin b2 hb2 hib2; omega
  by_cases h : adj G b1 b2
  · constructor
    · intro hf _
      exact hf b1 hb1 hib1 hb1j hne (adj_comm.mp h)
    · intro hn
      exfalso
      apply hn
      intro q hq hiq hqj hqb1
      by_cases hqb2 : q = b2
      · rw [hqb2]; exact h
      · have h3 : q < b2 := by have := hbmax q hq hqj; omega
        have h4 : b1 < q := by have := hbmin q hq hiq; omega
        exact (hc.no010 hb1 hq hb2 hj (by omega) (by omega) (by omega) h3 hb2j h).resolve_right h1j
  · constructor
    · intro _ he
      exact h (he b2 hb2 hib2 hb2j (Ne.symm hne))
    · intro _ q hq hiq hqj hqb2 hadj
      by_cases hqb1 : q = b1
      · exact h (adj_comm.mp (hqb1 ▸ hadj))
      · have h3 : q < b2 := by have := hbmax q hq hqj; omega
        have h4 : b1 < q := by have := hbmin q hq hiq; omega
        rcases hc.no010 hb2 hb1 hq hj (by omega) (by omega) (by omega) h4 hqj hadj with h5 | h5
        · exact h (adj_comm.mp h5)
        · exact h2j h5

/-! ### Deleting a vertex of `A` or `C` -/

/-- Deleting the smallest vertex of `C` when it sees all of `A` and nothing of `C`. -/
theorem DD_del_c {S : Finset ℕ} {i j c : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hc' : c ∈ S) (hjc : j < c) (hcmin : ∀ q ∈ S, j < q → c ≤ q) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ((∀ q ∈ S, q < i → adj G c q) ∧ (∀ q ∈ S, j < q → q ≠ c → ¬ adj G c q))).card
      = (clsSet (S.erase c) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => q < i) _ hi hj hc' (by omega) (by omega)
  · show (i < i) ↔ iD i j c
    arith
  · show (j < i) ↔ jD i c
    arith
  · intro G hG hc hcond q hq hqc
    have h1 : ¬ adj G c i := fun h => by have := (hc.adj_i hc').mp h; arith
    have h2 : ¬ adj G c j := fun h => by have := (hc.adj_j hc').mp h; arith
    show adj G c q ↔ q < i
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun h => absurd h h1, fun h => by omega⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun h => absurd h h2, fun h => by omega⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · exact ⟨fun _ => hlt, fun _ => hcond.1 q hq hlt⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · refine ⟨fun h => ?_, fun h => by omega⟩
        rcases hc.no010 hc' hi hq hj (by omega) hqc (by omega) (by omega) hlt2 h with h3 | h3
        · exact absurd h3 h1
        · exact absurd h3 h2
      · exact ⟨fun h => absurd h (hcond.2 q hq (by omega) hqc), fun h => by omega⟩
  · intro H hH hc
    constructor
    · apply cons_ins_clone_j hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jD S i j)
      · exact Or.inl (fun x _ y _ _ _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hcmin q hq
        omega
      · intro p _ h1 h2 h3
        show (p < i) ↔ jD i p
        arith
      · show (i < i) ↔ iD i j c
        arith
      · show (j < i) ↔ jD i c
        arith
    · constructor
      · intro q hq h1
        exact (adj_ins_self hH hq (by omega)).mpr h1
      · intro q hq h1 h2 h
        have := (adj_ins_self hH hq h2).mp h
        omega

/-- Deleting the largest vertex of `A` when it sees the rest of `A` and nothing of `C`. -/
theorem DD_del_amax {S : Finset ℕ} {i j a : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (ha : a ∈ S) (hai : a < i) (hamax : ∀ q ∈ S, q < i → q ≤ a) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ((∀ q ∈ S, q < i → q ≠ a → adj G a q) ∧ (∀ q ∈ S, j < q → ¬ adj G a q))).card
      = (clsSet (S.erase a) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => q ≤ j ∧ q ≠ a) _ hi hj ha (by omega) (by omega)
  · show (i ≤ j ∧ i ≠ a) ↔ iD i j a
    arith
  · show (j ≤ j ∧ j ≠ a) ↔ jD i a
    arith
  · intro G hG hc hcond q hq hqa
    have h1 : adj G a i := (hc.adj_i ha).mpr (by arith)
    have h2 : adj G a j := (hc.adj_j ha).mpr (by arith)
    show adj G a q ↔ (q ≤ j ∧ q ≠ a)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun _ => by omega, fun _ => h2⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · exact ⟨fun _ => by omega, fun _ => hcond.1 q hq hlt hqa⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega,
          fun _ => hc.no101 ha hi hq hj (by omega) hqa (by omega) (by omega) hlt2 h1 h2⟩
      · exact ⟨fun h => absurd h (hcond.2 q hq (by omega)), fun h => by omega⟩
  · intro H hH hc
    constructor
    · apply cons_ins_clone_i hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jD S i j)
      · exact Or.inl (fun x _ y _ hxa _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hamax q hq
        omega
      · intro p _ h1 h2 h3
        show (p ≤ j ∧ p ≠ a) ↔ iD i j p
        arith
      · show (i ≤ j ∧ i ≠ a) ↔ iD i j a
        arith
      · show (j ≤ j ∧ j ≠ a) ↔ jD i a
        arith
    · constructor
      · intro q hq h1 h2
        exact (adj_ins_self hH hq h2).mpr ⟨by omega, h2⟩
      · intro q hq h1 h
        have := (adj_ins_self hH hq (by omega)).mp h
        omega

theorem DD_dich_ac {S : Finset ℕ} {G : Graph} {i j a c : ℕ}
    (hc : Cls S i j (iD i j) (jD i) G) (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (ha : a ∈ S) (hai : a < i) (hamax : ∀ q ∈ S, q < i → q ≤ a)
    (hc' : c ∈ S) (hjc : j < c) (hcmin : ∀ q ∈ S, j < q → c ≤ q) :
    ((∀ q ∈ S, q < i → q ≠ a → adj G a q) ∧ (∀ q ∈ S, j < q → ¬ adj G a q)) ↔
      ¬ ((∀ q ∈ S, q < i → adj G c q) ∧ (∀ q ∈ S, j < q → q ≠ c → ¬ adj G c q)) := by
  have hai' : adj G a i := (hc.adj_i ha).mpr (by arith)
  have hci' : ¬ adj G c i := fun h => by have := (hc.adj_i hc').mp h; arith
  have hcj' : ¬ adj G c j := fun h => by have := (hc.adj_j hc').mp h; arith
  by_cases h : adj G a c
  · constructor
    · intro hh _
      exact hh.2 c hc' hjc h
    · intro hn
      exfalso
      apply hn
      constructor
      · intro q hq hqi
        by_cases hqa : q = a
        · rw [hqa]; exact adj_comm.mp h
        · have hlt : q < a := by have := hamax q hq hqi; omega
          exact (hc.no010 hc' hq ha hi (by omega) (by omega) (by omega) hlt hai
            (adj_comm.mp h)).resolve_right hci'
      · intro q hq hjq hqc hadj
        have hlt : c < q := by have := hcmin q hq hjq; omega
        exact hcj' (hc.no101 hc' ha hj hq (by omega) (by omega) (by omega) (by omega) hjq
          (adj_comm.mp h) hadj)
  · constructor
    · intro _ hg
      exact h (adj_comm.mp (hg.1 a ha hai))
    · intro _
      constructor
      · intro q hq hqi hqa
        have hlt : q < a := by have := hamax q hq hqi; omega
        exact (hc.no010 ha hq hi hc' (by omega) (by omega) (by omega) hqi (by omega)
          hai').resolve_right h
      · intro q hq hjq hadj
        by_cases hqc : q = c
        · exact h (hqc ▸ hadj)
        · have hlt : c < q := by have := hcmin q hq hjq; omega
          exact h (hc.no101 ha hi hc' hq (by omega) (by omega) (by omega) (by omega) hlt hai' hadj)

/-! ### The two ends: only `A`, or only `C` -/

/-- With `B = C = ∅`: deleting the smallest vertex when it has no neighbour in `A`. -/
theorem DD_del_amin {S : Finset ℕ} {i j a : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (ha : a ∈ S) (hai : a < i) (hamin : ∀ q ∈ S, a ≤ q)
    (hnoB : ∀ q ∈ S, ¬ (i < q ∧ q < j)) (hmaxj : ∀ q ∈ S, q ≤ j) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ∀ q ∈ S, q < i → q ≠ a → ¬ adj G a q).card
      = (clsSet (S.erase a) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => i ≤ q) _ hi hj ha (by omega) (by omega)
  · show (i ≤ i) ↔ iD i j a
    arith
  · show (i ≤ j) ↔ jD i a
    arith
  · intro G hG hc hcond q hq hqa
    have h1 : adj G a i := (hc.adj_i ha).mpr (by arith)
    have h2 : adj G a j := (hc.adj_j ha).mpr (by arith)
    show adj G a q ↔ i ≤ q
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun _ => by omega, fun _ => h2⟩
    have h3 := hnoB q hq
    have h4 := hmaxj q hq
    have hlt : q < i := by omega
    exact ⟨fun h => absurd h (hcond q hq hlt hqa), fun h => by omega⟩
  · intro H hH hc
    constructor
    · intro p hp
      by_cases hpa : p = a
      · rw [hpa]
        exact mono_ins_self hH (Or.inr (fun x _ y _ _ _ hxy hx => by omega))
      by_cases hpi : p = i
      · rw [hpi]
        exact mono_ins_marked hH hc.rowi hi (by omega) (by show (i ≤ i) ↔ iD i j a; arith)
          (mono_iD S i j)
      by_cases hpj : p = j
      · rw [hpj]
        exact mono_ins_marked hH hc.rowj hj (by omega) (by show (i ≤ j) ↔ jD i a; arith)
          (mono_jD S i j)
      have hpe : p ∈ S.erase a := mem_erase.mpr ⟨hpa, hp⟩
      have h3 := hnoB p hp
      have h4 := hmaxj p hp
      have hlt : p < i := by omega
      have hje : j ∈ S.erase a := mem_erase.mpr ⟨by omega, hj⟩
      have hup : UpP (S.erase a) p (adj H p) :=
        upP_of_top hje (Ne.symm hpj) (fun q hq => hmaxj q (mem_erase.mp hq).2)
          ((hc.adj_j hpe).mpr (by arith)) (hc.cons p hpe)
      right
      refine upP_ins_min (fun q hq hqa => by have := hamin q hq; omega) ?_ ?_ hup
      · intro q _ hqa
        exact adj_ins_of_ne hpa hqa
      · rw [adj_ins_new hH hp hpa]
        omega
    · intro q hq h1 h2 h
      have := (adj_ins_self hH hq h2).mp h
      omega

theorem DD_dich_a {S : Finset ℕ} {G : Graph} {i j a1 a2 : ℕ}
    (hc : Cls S i j (iD i j) (jD i) G) (hi : i ∈ S) (_hj : j ∈ S) (hij : i < j)
    (ha1 : a1 ∈ S) (ha1i : a1 < i) (hamin : ∀ q ∈ S, a1 ≤ q)
    (ha2 : a2 ∈ S) (ha2i : a2 < i) (hamax : ∀ q ∈ S, q < i → q ≤ a2)
    (hmaxj : ∀ q ∈ S, q ≤ j) (hne : a1 ≠ a2) :
    (∀ q ∈ S, q < i → q ≠ a1 → ¬ adj G a1 q) ↔
      ¬ ((∀ q ∈ S, q < i → q ≠ a2 → adj G a2 q) ∧ (∀ q ∈ S, j < q → ¬ adj G a2 q)) := by
  have h1i : adj G a1 i := (hc.adj_i ha1).mpr (by arith)
  have h2i : adj G a2 i := (hc.adj_i ha2).mpr (by arith)
  have hlt12 : a1 < a2 := by have := hamin a2 ha2; omega
  by_cases h : adj G a1 a2
  · constructor
    · intro hf _
      exact hf a2 ha2 ha2i (Ne.symm hne) h
    · intro hn
      exfalso
      apply hn
      constructor
      · intro q hq hqi hqa2
        by_cases hqa1 : q = a1
        · rw [hqa1]; exact adj_comm.mp h
        · have h3 : a1 < q := by have := hamin q hq; omega
          have h4 : q < a2 := by have := hamax q hq hqi; omega
          exact hc.no101 ha2 ha1 hq hi (by omega) (by omega) (by omega) h3 hqi (adj_comm.mp h) h2i
      · intro q hq hjq
        have := hmaxj q hq
        omega
  · constructor
    · intro _ hh
      exact h (adj_comm.mp (hh.1 a1 ha1 ha1i hne))
    · intro _ q hq hqi hqa1 hadj
      by_cases hqa2 : q = a2
      · exact h (hqa2 ▸ hadj)
      · have h3 : a1 < q := by have := hamin q hq; omega
        have h4 : q < a2 := by have := hamax q hq hqi; omega
        exact h (hc.no101 ha1 hq ha2 hi (by omega) (by omega) (by omega) h4 ha2i hadj h1i)

/-- With `A = B = ∅`: deleting the largest vertex when it is joined to the rest of `C`. -/
theorem DD_del_cmax {S : Finset ℕ} {i j c : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hc' : c ∈ S) (hjc : j < c) (hcmax : ∀ q ∈ S, q ≤ c)
    (hnoB : ∀ q ∈ S, ¬ (i < q ∧ q < j)) (hmini : ∀ q ∈ S, i ≤ q) :
    (sel S fun G => Cls S i j (iD i j) (jD i) G ∧
        ∀ q ∈ S, j < q → q ≠ c → adj G c q).card
      = (clsSet (S.erase c) i j (iD i j) (jD i)).card := by
  apply cls_del_card (fun q => j < q) _ hi hj hc' (by omega) (by omega)
  · show (j < i) ↔ iD i j c
    arith
  · show (j < j) ↔ jD i c
    arith
  · intro G hG hc hcond q hq hqc
    have h1 : ¬ adj G c i := fun h => by have := (hc.adj_i hc').mp h; arith
    have h2 : ¬ adj G c j := fun h => by have := (hc.adj_j hc').mp h; arith
    show adj G c q ↔ j < q
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun h => absurd h h1, fun h => by omega⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun h => absurd h h2, fun h => by omega⟩
    have h3 := hnoB q hq
    have h4 := hmini q hq
    have hlt : j < q := by omega
    exact ⟨fun _ => hlt, fun _ => hcond q hq hlt hqc⟩
  · intro H hH hc
    constructor
    · intro p hp
      by_cases hpc : p = c
      · rw [hpc]
        exact mono_ins_self hH (Or.inr (fun x _ y _ _ _ hxy hx => by omega))
      by_cases hpi : p = i
      · rw [hpi]
        exact mono_ins_marked hH hc.rowi hi (by omega) (by show (j < i) ↔ iD i j c; arith)
          (mono_iD S i j)
      by_cases hpj : p = j
      · rw [hpj]
        exact mono_ins_marked hH hc.rowj hj (by omega) (by show (j < j) ↔ jD i c; arith)
          (mono_jD S i j)
      have hpe : p ∈ S.erase c := mem_erase.mpr ⟨hpc, hp⟩
      have h3 := hnoB p hp
      have h4 := hmini p hp
      have hlt : j < p := by omega
      have hie : i ∈ S.erase c := mem_erase.mpr ⟨by omega, hi⟩
      have hup : UpP (S.erase c) p (adj H p) :=
        upP_of_bot hie (Ne.symm hpi) (fun q hq => hmini q (mem_erase.mp hq).2)
          (fun h => by have := (hc.adj_i hpe).mp h; arith) (hc.cons p hpe)
      right
      refine upP_ins_max (fun q hq hqc => by have := hcmax q hq; omega) ?_ ?_ hup
      · intro q _ hqc
        exact adj_ins_of_ne hpc hqc
      · rw [adj_ins_new hH hp hpc]
        exact hlt
    · intro q hq h1 h2
      exact (adj_ins_self hH hq h2).mpr h1

theorem DD_dich_c {S : Finset ℕ} {G : Graph} {i j c1 c2 : ℕ}
    (hc : Cls S i j (iD i j) (jD i) G) (_hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hc1 : c1 ∈ S) (hjc1 : j < c1) (hcmin : ∀ q ∈ S, j < q → c1 ≤ q)
    (hc2 : c2 ∈ S) (hjc2 : j < c2) (hcmax : ∀ q ∈ S, q ≤ c2)
    (hmini : ∀ q ∈ S, i ≤ q) (hne : c1 ≠ c2) :
    ((∀ q ∈ S, q < i → adj G c1 q) ∧ (∀ q ∈ S, j < q → q ≠ c1 → ¬ adj G c1 q)) ↔
      ¬ (∀ q ∈ S, j < q → q ≠ c2 → adj G c2 q) := by
  have h1j : ¬ adj G c1 j := fun h => by have := (hc.adj_j hc1).mp h; arith
  have h2j : ¬ adj G c2 j := fun h => by have := (hc.adj_j hc2).mp h; arith
  have hlt12 : c1 < c2 := by have := hcmax c1 hc1; omega
  by_cases h : adj G c1 c2
  · constructor
    · intro hg _
      exact hg.2 c2 hc2 hjc2 (Ne.symm hne) h
    · intro hn
      exfalso
      apply hn
      intro q hq hjq hqc2
      by_cases hqc1 : q = c1
      · rw [hqc1]; exact adj_comm.mp h
      · have h3 : c1 < q := by have := hcmin q hq hjq; omega
        have h4 : q < c2 := by have := hcmax q hq; omega
        exact (hc.no010 hc2 hj hc1 hq (by omega) (by omega) (by omega) hjc1 h3
          (adj_comm.mp h)).resolve_left h2j
  · constructor
    · intro _ hk
      exact h (adj_comm.mp (hk c1 hc1 hjc1 hne))
    · intro _
      constructor
      · intro q hq hqi
        have := hmini q hq
        omega
      · intro q hq hjq hqc1 hadj
        by_cases hqc2 : q = c2
        · exact h (hqc2 ▸ hadj)
        · have h3 : c1 < q := by have := hcmin q hq hjq; omega
          have h4 : q < c2 := by have := hcmax q hq; omega
          rcases hc.no010 hc1 hj hq hc2 (by omega) (by omega) (by omega) hjq h4 hadj with h5 | h5
          · exact h1j h5
          · exact h h5

end

end ZonoFlips
