import PottsBPSource

/-! Nonconvexity from the exposed face of a colour missed by all the pinning configurations. -/
namespace PottsBP
open scoped BigOperators
open Finset

private lemma product_le_factor {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) {k : ι} (hk : k ∈ s) :
    ∏ i ∈ s, f i ≤ f k := by
  rw [← mul_prod_erase s f hk]
  exact mul_le_of_le_one_right (h0 k) (Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i))

private lemma tight_product_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1)
    (he : (∏ i, (1-f i)) = 1 - ∑ i, f i) {j k : ι} (hj : 0 < f j) (hk : k ≠ j) :
    f k = 0 := by
  let s := (univ : Finset ι).erase j
  let R := ∏ i ∈ s, (1-f i)
  have hl := product_lower s f h0 h1
  have hu : R ≤ 1 := Finset.prod_le_one (fun i _ => sub_nonneg.mpr (h1 i))
    (fun i _ => by linarith [h0 i])
  rw [← mul_prod_erase univ (fun i => 1-f i) (mem_univ j),
    ← add_sum_erase univ f (mem_univ j)] at he
  change (1-f j)*R = 1-(f j + ∑ i ∈ s, f i) at he
  change 1 - ∑ i ∈ s, f i ≤ R at hl
  have hz : f j * (1-R) = 0 := by nlinarith [mul_nonneg (h0 j) (sub_nonneg.mpr hu)]
  have hr := (mul_eq_zero.mp hz).resolve_left hj.ne'
  have hk' : k ∈ s := mem_erase.mpr ⟨hk,mem_univ k⟩
  have hh : R ≤ 1 - f k := product_le_factor s _ (fun i => sub_nonneg.mpr (h1 i))
    (fun i => by linarith [h0 i]) hk'
  linarith [h0 k]

private def pins {q d : ℕ} (f : Fin d ↪ Fin q) (j : Fin d) (i : Fin q) : ℝ :=
  if f j = i then 1 else 0

private lemma pins_simplex {q d : ℕ} (f : Fin d ↪ Fin q) (j : Fin d) :
    simplexN (pins f j) := by
  constructor
  · intro i
    simp [pins]
    split <;> norm_num
  · simp [pins]

private lemma pins_weight {q d : ℕ} (β : ℝ) (f : Fin d ↪ Fin q) (i : Fin q) :
    rawWeight β (pins f) i = if (∃ j, f j = i) then β else 1 := by
  classical
  calc
    _ = ∏ j, (if f j = i then β else 1) := by
      apply prod_congr rfl
      intro j _
      by_cases h : f j = i <;> simp [pins, h]
    _ = _ := Fintype.prod_ite_eq_ite_exists _ (fun _ _ a b => f.injective (a.trans b.symm)) β

private lemma pins_partition {q d : ℕ} (β : ℝ) (f : Fin d ↪ Fin q) :
    (∑ i, rawWeight β (pins f) i) = (q : ℝ) - d * (1-β) := by
  classical
  rw [← sum_linear_weights β (pins_simplex f)]
  apply sum_congr rfl
  intro i _
  rw [pins_weight]
  simp only [pins, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq_ite_exists (fun j => f j = i) (fun _ _ a b => f.injective (a.trans b.symm))]
  split <;> ring

theorem nonconvex_general {q d : ℕ} (hd : 2 ≤ d) (hq : d+2 ≤ q) {β : ℝ}
    (h0 : 0 ≤ β) (h1 : β < 1) : ¬ Convex ℝ (generalImage q d β) := by
  classical
  intro hc
  let active : Fin (d+1) ↪ Fin q := Fin.castLEEmb (by omega)
  let extra : Fin q := ⟨d+1, by omega⟩
  let assign (k : Fin (d+1)) := (Fin.succAboveEmb k).trans active
  let Z : ℝ := q - d*(1-β)
  let c : ℝ := 1 / ((d : ℝ)+1)
  let X (k : Fin (d+1)) := generalBP β (pins (assign k))
  let w := ∑ k, c • X k
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq' : (d : ℝ) + 2 ≤ q := by exact_mod_cast hq
  have hZ : 0 < Z := by dsimp [Z]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ d) h0]
  have ht : 0 < 1-β := sub_pos.mpr h1
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc1 : ((d : ℝ)+1)*c = 1 := by dsimp [c]; field_simp
  have hsum : (∑ _ : Fin (d+1), c) = 1 := by simpa using hc1
  have hx (k) : X k ∈ generalImage q d β := by
    refine ⟨pins (assign k),pins_simplex _,?_,rfl⟩
    rw [pins_partition]; exact hZ
  have hw : w ∈ generalImage q d β :=
    hc.sum_mem (fun _ _ => hcpos.le) hsum (fun k _ => hx k)
  have avg (i : Fin q) : w i * Z = ∑ k, c * rawWeight β (pins (assign k)) i := by
    simp only [w, sum_apply, Pi.smul_apply, smul_eq_mul, X, generalBP, pins_partition, sum_mul]
    apply sum_congr rfl
    intro k _
    change c * (rawWeight β (pins (assign k)) i / Z) * Z = _
    field_simp
  have hext (k : Fin (d+1)) : ¬ ∃ j, assign k j = extra := by
    rintro ⟨j,h⟩
    have hj := (k.succAbove j).isLt
    have h' := congrArg Fin.val h
    change (k.succAbove j).val = d+1 at h'
    omega
  have we : w extra * Z = 1 := by
    simpa [pins_weight, hext, hsum] using avg extra
  have used (k i : Fin (d+1)) : (∃ j, assign k j = active i) ↔ i ≠ k := by
    change (∃ j, active (k.succAbove j) = active i) ↔ _
    simp only [EmbeddingLike.apply_eq_iff_eq]
    exact Fin.exists_succAbove_eq_iff
  have wa (i : Fin (d+1)) : w (active i) * Z = β + c*(1-β) := by
    rw [avg]
    calc
      _ = ∑ k : Fin (d+1), (c*β + if i = k then c*(1-β) else 0) := by
        apply sum_congr rfl
        intro k _
        rw [pins_weight, if_congr (used k i) rfl rfl]
        by_cases h : i = k
        · simp [h]
          ring
        · simp [h]
      _ = _ := by simp [sum_add_distrib]; nlinarith only [congrArg (· * β) hc1]
  obtain ⟨p,hp,hpos,hpw⟩ := hw
  let S := ∑ i, rawWeight β p i
  have eqn (i) : rawWeight β p i = w i * S :=
    (div_eq_iff (ne_of_gt hpos)).mp (congrFun hpw i)
  have hepos : 0 < w extra := pos_of_mul_pos_left (we.symm ▸ zero_lt_one) hZ.le
  have hue : rawWeight β p extra ≤ 1 := Finset.prod_le_one
    (fun j _ => sub_nonneg.mpr (scaled_entry_bounds h0 h1.le hp j extra).2)
    (fun j _ => sub_le_self _ (scaled_entry_bounds h0 h1.le hp j extra).1)
  have hS : S = Z := by
    apply le_antisymm _ (partition_lower_bound h0 h1.le hp)
    exact (mul_le_mul_left hepos).mp (by rw [← eqn, we]; exact hue)
  have tight (i) : rawWeight β p i = 1 - ∑ j, (1-β) * p j i := by
    have hle (b) := product_lower univ (fun j => (1-β)*p j b)
      (fun j => (scaled_entry_bounds h0 h1.le hp j b).1)
      (fun j => (scaled_entry_bounds h0 h1.le hp j b).2)
    apply le_antisymm _ (hle i)
    by_contra! hi
    have hlt := sum_lt_sum (fun b _ => hle b) ⟨i, mem_univ i, hi⟩
    change (∑ b, (1 - ∑ j, (1-β)*p j b)) < S at hlt
    rw [sum_linear_weights β hp, hS] at hlt
    exact (lt_irrefl Z) hlt
  have column (i : Fin (d+1)) : (∑ j, p j (active i)) = 1 - c := by
    have he := eqn (active i)
    rw [hS, wa, tight, ← mul_sum] at he
    exact (mul_left_cancel₀ ht.ne') (by linarith only [he] : (1-β)*(∑ j, p j (active i)) = (1-β)*(1-c))
  have hhalf : (1/2 : ℝ) < 1-c := by
    dsimp [c]
    have hh : (1:ℝ)/((d:ℝ)+1) < 1/2 := (div_lt_iff₀ (by positivity)).2 (by linarith)
    linarith
  have owner_exists (i : Fin (d+1)) : ∃ j, 0 < p j (active i) := by
    by_contra! h
    have hall (j) : p j (active i) = 0 := le_antisymm (h j) ((hp j).1 _)
    have := column i
    simp [hall] at this
    linarith
  choose owner ho using owner_exists
  have owns (i) : p (owner i) (active i) = 1-c := by
    rw [← column i]
    symm
    apply sum_eq_single (owner i)
    · intro k _ hk
      have hh := tight_product_disjoint (fun j => (1-β)*p j (active i))
        (fun j => (scaled_entry_bounds h0 h1.le hp j (active i)).1)
        (fun j => (scaled_entry_bounds h0 h1.le hp j (active i)).2)
        (tight (active i)) (mul_pos ht (ho i)) hk
      exact (mul_eq_zero.mp hh).resolve_left ht.ne'
    · simp
  have hinj : Function.Injective owner := by
    intro i k hik
    by_contra hne
    have hdiff : active i ≠ active k := fun h => hne (active.injective h)
    have hle := sum_le_sum_of_subset_of_nonneg (s := {active i,active k}) (t := univ)
      (subset_univ _) (fun b _ _ => (hp (owner i)).1 b)
    rw [sum_pair hdiff, (hp (owner i)).2, owns i, hik, owns k] at hle
    linarith
  have hcard := Fintype.card_le_of_injective owner hinj
  simp at hcard

theorem source_nonconvex_general {q d : ℕ} (hd : 2 ≤ d) (hq : d+2 ≤ q) {β : ℝ}
    (h0 : 0 ≤ β) (h1 : β < 1) : ¬ Convex ℝ (sourceImage q d β) := by
  have hh : 1 ≤ (q:ℝ)/(d+1) := (le_div_iff₀ (by positivity)).2 (by
    have : (d:ℝ)+2 ≤ q := by exact_mod_cast hq
    linarith)
  rw [sourceImage_eq_generalImage (by omega) (max_le h0 (by linarith)) h1.le]
  exact nonconvex_general hd hq h0 h1

end PottsBP
