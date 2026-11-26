import ZonotopeFlips.Classes

/-!
# The class `DU`: `N(i) = {q < j} \ {i}` and `N(j) = {q > i} \ {j}`

For `i < j` in `S`, write `A`, `B`, `C` for the vertices below `i`, between `i` and `j`, and
above `j`.  The number of consistent graphs in which `i` is joined exactly to the vertices
below `j` and `j` exactly to the vertices above `i` is `choose (|A| + |B| + |C|) |B|`.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

/-! ### The four row prescriptions -/

/-- `i` is joined to everything below `j`. -/
def iD (i j : ℕ) (q : ℕ) : Prop := q < j ∧ q ≠ i
/-- `i` is joined to everything above `j`. -/
def iU (j : ℕ) (q : ℕ) : Prop := j < q
/-- `j` is joined to everything below `i`. -/
def jD (i : ℕ) (q : ℕ) : Prop := q < i
/-- `j` is joined to everything above `i`. -/
def jU (i j : ℕ) (q : ℕ) : Prop := i < q ∧ q ≠ j

/-- Unfold the row prescriptions and finish by linear arithmetic. -/
macro "arith" : tactic => `(tactic| ((try simp only [iD, iU, jD, jU] at *) <;> omega))

theorem mono_iD (S : Finset ℕ) (i j : ℕ) : MonoP S i (iD i j) :=
  Or.inl (fun x _ y _ hxi _ hxy hy => by arith)

theorem mono_iU (S : Finset ℕ) (i j : ℕ) : MonoP S i (iU j) :=
  Or.inr (fun x _ y _ _ _ hxy hx => by arith)

theorem mono_jD (S : Finset ℕ) (i j : ℕ) : MonoP S j (jD i) :=
  Or.inl (fun x _ y _ _ _ hxy hy => by arith)

theorem mono_jU (S : Finset ℕ) (i j : ℕ) : MonoP S j (jU i j) :=
  Or.inr (fun x _ y _ _ hyj hxy hx => by arith)

/-! ### Sizes of the three blocks -/

def nA (S : Finset ℕ) (i : ℕ) : ℕ := (S.filter fun q => q < i).card
def nB (S : Finset ℕ) (i j : ℕ) : ℕ := (S.filter fun q => i < q ∧ q < j).card
def nC (S : Finset ℕ) (j : ℕ) : ℕ := (S.filter fun q => j < q).card

theorem card_filter_erase_pos {S : Finset ℕ} {w : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hw : w ∈ S) (hP : P w) : ((S.erase w).filter P).card + 1 = (S.filter P).card := by
  have e : (S.erase w).filter P = (S.filter P).erase w := by
    ext q; simp only [mem_filter, mem_erase]; tauto
  rw [e]
  exact card_erase_add_one (mem_filter.mpr ⟨hw, hP⟩)

theorem card_filter_erase_neg {S : Finset ℕ} {w : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hP : ¬ P w) : ((S.erase w).filter P).card = (S.filter P).card := by
  congr 1
  ext q
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨fun e => hP (e ▸ hp), h⟩, hp⟩

theorem exists_max_of_nonempty {S : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : (S.filter P).Nonempty) : ∃ a, a ∈ S ∧ P a ∧ ∀ q ∈ S, P q → q ≤ a :=
  ⟨(S.filter P).max' h, (mem_filter.mp (max'_mem _ h)).1, (mem_filter.mp (max'_mem _ h)).2,
    fun q hq hP => le_max' _ q (mem_filter.mpr ⟨hq, hP⟩)⟩

theorem exists_min_of_nonempty {S : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : (S.filter P).Nonempty) : ∃ a, a ∈ S ∧ P a ∧ ∀ q ∈ S, P q → a ≤ q :=
  ⟨(S.filter P).min' h, (mem_filter.mp (min'_mem _ h)).1, (mem_filter.mp (min'_mem _ h)).2,
    fun q hq hP => min'_le _ q (mem_filter.mpr ⟨hq, hP⟩)⟩

theorem forall_not_of_not_nonempty {S : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : ¬ (S.filter P).Nonempty) : ∀ q ∈ S, ¬ P q := by
  intro q hq hP
  exact h ⟨q, mem_filter.mpr ⟨hq, hP⟩⟩

theorem card_zero_of_not_nonempty {S : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : ¬ (S.filter P).Nonempty) : (S.filter P).card = 0 := by
  rw [card_eq_zero]; exact not_nonempty_iff_eq_empty.mp h

/-! ### The four deletion steps -/

/-- Deleting the largest vertex of `A` when it is joined to all of `B`. -/
theorem DU_del_a {S : Finset ℕ} {i j a : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (ha : a ∈ S) (hai : a < i) (hamax : ∀ q ∈ S, q < i → q ≤ a) :
    (sel S fun G => Cls S i j (iD i j) (jU i j) G ∧ ∀ q ∈ S, i < q → q < j → adj G a q).card
      = (clsSet (S.erase a) i j (iD i j) (jU i j)).card := by
  apply cls_del_card (fun q => q < j ∧ q ≠ a) _ hi hj ha (by omega) (by omega)
  · show (i < j ∧ i ≠ a) ↔ iD i j a
    arith
  · show (j < j ∧ j ≠ a) ↔ jU i j a
    arith
  · intro G hG hc hcond q hq hqa
    have h1 : adj G a i := (hc.adj_i ha).mpr (by arith)
    have h2 : ¬ adj G a j := fun h => by have := (hc.adj_j ha).mp h; arith
    show adj G a q ↔ (q < j ∧ q ≠ a)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun h => absurd h h2, fun h => by omega⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · have := hc.no010 ha hq hi hj hqa (by omega) (by omega) hlt hij h1
      exact ⟨fun _ => by omega, fun _ => this.resolve_right h2⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega, fun _ => hcond q hq (by omega) hlt2⟩
      · refine ⟨fun h => ?_, fun h => by omega⟩
        exact absurd (hc.no101 ha hi hj hq (by omega) (by omega) hqa hij (by omega) h1 h) h2
  · intro H hH hc
    constructor
    · apply cons_ins_clone_i hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jU S i j)
      · exact Or.inl (fun x _ y _ hxa _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hamax q hq
        omega
      · intro p _ h1 h2 h3
        show (p < j ∧ p ≠ a) ↔ iD i j p
        arith
      · show (i < j ∧ i ≠ a) ↔ iD i j a
        arith
      · show (j < j ∧ j ≠ a) ↔ jU i j a
        arith
    · intro q hq h1 h2
      exact (adj_ins_self hH hq (by omega)).mpr ⟨h2, by omega⟩

/-- Deleting the largest vertex of `B` when it has no neighbour in `A` and sees all of `C`. -/
theorem DU_del_b {S : Finset ℕ} {i j b : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmax : ∀ q ∈ S, q < j → q ≤ b) :
    (sel S fun G => Cls S i j (iD i j) (jU i j) G ∧
        ((∀ q ∈ S, q < i → ¬ adj G b q) ∧ (∀ q ∈ S, j < q → adj G b q))).card
      = (clsSet (S.erase b) i j (iD i j) (jU i j)).card := by
  apply cls_del_card (fun q => i ≤ q ∧ q ≠ b) _ hi hj hb (by omega) (by omega)
  · show (i ≤ i ∧ i ≠ b) ↔ iD i j b
    arith
  · show (i ≤ j ∧ j ≠ b) ↔ jU i j b
    arith
  · intro G hG hc hcond q hq hqb
    have h1 : adj G b i := (hc.adj_i hb).mpr (by arith)
    have h2 : adj G b j := (hc.adj_j hb).mpr (by arith)
    show adj G b q ↔ (i ≤ q ∧ q ≠ b)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun _ => by omega, fun _ => h2⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · exact ⟨fun h => absurd h (hcond.1 q hq hlt), fun h => by omega⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega,
          fun _ => hc.no101 hb hi hq hj (by omega) hqb (by omega) (by omega) hlt2 h1 h2⟩
      · exact ⟨fun _ => by omega, fun _ => hcond.2 q hq (by omega)⟩
  · intro H hH hc
    constructor
    · apply cons_ins_clone_j hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jU S i j)
      · exact Or.inr (fun x _ y _ _ hyb hxy hx => by omega)
      · intro q hq h1 h2
        have := hbmax q hq
        omega
      · intro p _ h1 h2 h3
        show (i ≤ p ∧ p ≠ b) ↔ jU i j p
        arith
      · show (i ≤ i ∧ i ≠ b) ↔ iD i j b
        arith
      · show (i ≤ j ∧ j ≠ b) ↔ jU i j b
        arith
    · constructor
      · intro q hq h1 h
        have := (adj_ins_self hH hq (by omega)).mp h
        omega
      · intro q hq h1
        exact (adj_ins_self hH hq (by omega)).mpr ⟨by omega, by omega⟩

/-- Deleting the smallest vertex of `C` when it is joined to all of `B`. -/
theorem DU_del_c {S : Finset ℕ} {i j c : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hc' : c ∈ S) (hjc : j < c) (hcmin : ∀ q ∈ S, j < q → c ≤ q) :
    (sel S fun G => Cls S i j (iD i j) (jU i j) G ∧ ∀ q ∈ S, i < q → q < j → adj G c q).card
      = (clsSet (S.erase c) i j (iD i j) (jU i j)).card := by
  apply cls_del_card (fun q => i < q ∧ q ≠ c) _ hi hj hc' (by omega) (by omega)
  · show (i < i ∧ i ≠ c) ↔ iD i j c
    arith
  · show (i < j ∧ j ≠ c) ↔ jU i j c
    arith
  · intro G hG hc hcond q hq hqc
    have h1 : ¬ adj G c i := fun h => by have := (hc.adj_i hc').mp h; arith
    have h2 : adj G c j := (hc.adj_j hc').mpr (by arith)
    show adj G c q ↔ (i < q ∧ q ≠ c)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun h => absurd h h1, fun h => by omega⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun _ => by omega, fun _ => h2⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · refine ⟨fun h => ?_, fun h => by omega⟩
      exact absurd (hc.no101 hc' hq hi hj hqc (by omega) (by omega) hlt hij h h2) h1
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega, fun _ => hcond q hq (by omega) hlt2⟩
      · have := hc.no010 hc' hi hj hq (by omega) (by omega) hqc hij (by omega) h2
        exact ⟨fun _ => by omega, fun _ => this.resolve_left h1⟩
  · intro H hH hc
    constructor
    · apply cons_ins_clone_j hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jU S i j)
      · exact Or.inr (fun x _ y _ _ hyc hxy hx => by omega)
      · intro q hq h1 h2
        have := hcmin q hq
        omega
      · intro p _ h1 h2 h3
        show (i < p ∧ p ≠ c) ↔ jU i j p
        arith
      · show (i < i ∧ i ≠ c) ↔ iD i j c
        arith
      · show (i < j ∧ j ≠ c) ↔ jU i j c
        arith
    · intro q hq h1 h2
      exact (adj_ins_self hH hq (by omega)).mpr ⟨h1, by omega⟩

/-- Deleting the smallest vertex of `B` when it has no neighbour in `C` and sees all of `A`. -/
theorem DU_del_d {S : Finset ℕ} {i j b : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmin : ∀ q ∈ S, i < q → b ≤ q) :
    (sel S fun G => Cls S i j (iD i j) (jU i j) G ∧
        ((∀ q ∈ S, j < q → ¬ adj G b q) ∧ (∀ q ∈ S, q < i → adj G b q))).card
      = (clsSet (S.erase b) i j (iD i j) (jU i j)).card := by
  apply cls_del_card (fun q => q ≤ j ∧ q ≠ b) _ hi hj hb (by omega) (by omega)
  · show (i ≤ j ∧ i ≠ b) ↔ iD i j b
    arith
  · show (j ≤ j ∧ j ≠ b) ↔ jU i j b
    arith
  · intro G hG hc hcond q hq hqb
    have h1 : adj G b i := (hc.adj_i hb).mpr (by arith)
    have h2 : adj G b j := (hc.adj_j hb).mpr (by arith)
    show adj G b q ↔ (q ≤ j ∧ q ≠ b)
    by_cases hqi : q = i
    · rw [hqi]; exact ⟨fun _ => by omega, fun _ => h1⟩
    by_cases hqj : q = j
    · rw [hqj]; exact ⟨fun _ => by omega, fun _ => h2⟩
    rcases Nat.lt_or_ge q i with hlt | hge
    · exact ⟨fun _ => by omega, fun _ => hcond.2 q hq hlt⟩
    · rcases Nat.lt_or_ge q j with hlt2 | hge2
      · exact ⟨fun _ => by omega,
          fun _ => hc.no101 hb hi hq hj (by omega) hqb (by omega) (by omega) hlt2 h1 h2⟩
      · exact ⟨fun h => absurd h (hcond.1 q hq (by omega)), fun h => by omega⟩
  · intro H hH hc
    constructor
    · apply cons_ins_clone_i hH hc hi hj (by omega) (by omega) _ _ (mono_iD S i j) (mono_jU S i j)
      · exact Or.inl (fun x _ y _ hxb _ hxy hy => by omega)
      · intro q hq h1 h2
        have := hbmin q hq
        omega
      · intro p _ h1 h2 h3
        show (p ≤ j ∧ p ≠ b) ↔ iD i j p
        arith
      · show (i ≤ j ∧ i ≠ b) ↔ iD i j b
        arith
      · show (j ≤ j ∧ j ≠ b) ↔ jU i j b
        arith
    · constructor
      · intro q hq h1 h
        have := (adj_ins_self hH hq (by omega)).mp h
        omega
      · intro q hq h1
        exact (adj_ins_self hH hq (by omega)).mpr ⟨by omega, by omega⟩

/-! ### The two dichotomies -/

theorem DU_dich_ab {S : Finset ℕ} {G : Graph} {i j a b : ℕ}
    (hc : Cls S i j (iD i j) (jU i j) G) (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (ha : a ∈ S) (hai : a < i) (hamax : ∀ q ∈ S, q < i → q ≤ a)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmax : ∀ q ∈ S, q < j → q ≤ b) :
    ((∀ q ∈ S, q < i → ¬ adj G b q) ∧ (∀ q ∈ S, j < q → adj G b q)) ↔
      ¬ (∀ q ∈ S, i < q → q < j → adj G a q) := by
  have haj' : ¬ adj G a j := fun h => by have := (hc.adj_j ha).mp h; arith
  have hbi' : adj G b i := (hc.adj_i hb).mpr (by arith)
  have hbj' : adj G b j := (hc.adj_j hb).mpr (by arith)
  by_cases hab : adj G a b
  · constructor
    · intro h _
      exact absurd (adj_comm.mp hab) (h.1 a ha hai)
    · intro h
      exfalso
      apply h
      intro q hq hiq hqj
      by_cases hqb : q = b
      · rw [hqb]; exact hab
      · have hlt : q < b := by have := hbmax q hq hqj; omega
        exact (hc.no010 ha hq hb hj (by omega) (by omega) (by omega) hlt hbj hab).resolve_right
          haj'
  · constructor
    · intro _ h
      exact hab (h b hb hib hbj)
    · intro _
      constructor
      · intro q hq hqi hbq
        by_cases hqa : q = a
        · exact hab (adj_comm.mp (hqa ▸ hbq))
        · have hlt : q < a := by have := hamax q hq hqi; omega
          exact hab (adj_comm.mp
            (hc.no101 hb hq ha hi (by omega) (by omega) (by omega) hlt hai hbq hbi'))
      · intro q hq hjq
        exact (hc.no010 hb ha hj hq (by omega) (by omega) (by omega) (by omega) hjq
          hbj').resolve_left (fun h => hab (adj_comm.mp h))

theorem DU_dich_cd {S : Finset ℕ} {G : Graph} {i j c b : ℕ}
    (hc : Cls S i j (iD i j) (jU i j) G) (hi : i ∈ S) (hj : j ∈ S) (hij : i < j)
    (hc' : c ∈ S) (hjc : j < c) (hcmin : ∀ q ∈ S, j < q → c ≤ q)
    (hb : b ∈ S) (hib : i < b) (hbj : b < j) (hbmin : ∀ q ∈ S, i < q → b ≤ q) :
    ((∀ q ∈ S, j < q → ¬ adj G b q) ∧ (∀ q ∈ S, q < i → adj G b q)) ↔
      ¬ (∀ q ∈ S, i < q → q < j → adj G c q) := by
  have hci' : ¬ adj G c i := fun h => by have := (hc.adj_i hc').mp h; arith
  have hbi' : adj G b i := (hc.adj_i hb).mpr (by arith)
  have hbj' : adj G b j := (hc.adj_j hb).mpr (by arith)
  by_cases hcb : adj G c b
  · constructor
    · intro h _
      exact absurd (adj_comm.mp hcb) (h.1 c hc' hjc)
    · intro h
      exfalso
      apply h
      intro q hq hiq hqj
      by_cases hqb : q = b
      · rw [hqb]; exact hcb
      · have hlt : b < q := by have := hbmin q hq hiq; omega
        exact (hc.no010 hc' hi hb hq (by omega) (by omega) (by omega) hib hlt hcb).resolve_left
          hci'
  · constructor
    · intro _ h
      exact hcb (h b hb hib hbj)
    · intro _
      constructor
      · intro q hq hjq hbq
        by_cases hqc : q = c
        · exact hcb (adj_comm.mp (hqc ▸ hbq))
        · have hlt : c < q := by have := hcmin q hq hjq; omega
          exact hcb (adj_comm.mp
            (hc.no101 hb hj hc' hq (by omega) (by omega) (by omega) hjc hlt hbj' hbq))
      · intro q hq hqi
        exact (hc.no010 hb hq hi hc' (by omega) (by omega) (by omega) hqi (by omega)
          hbi').resolve_right (fun h => hcb (adj_comm.mp h))

end

end ZonoFlips
