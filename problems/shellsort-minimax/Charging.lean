import Transport

namespace ShellMinimax
open Operational
variable {n h : Nat}

private theorem ins_on_prefix (a : Nat) (l : List Nat) :
    (ins a (chain l).1).2 = insertionCharge l.length (l.filter (· ≤ a)).length := by
  have hp : (chain l).1.Perm l := by rw [chain_values]; apply List.perm_insertionSort
  have hs : (chain l).1.Pairwise (· ≥ ·) := by rw [chain_values]; apply List.sorted_insertionSort
  simp only [ins_count _ _ hs, hp.length_eq, (hp.filter _).length_eq, insertionCharge]

private theorem mark_is_one (s : Finset (Fin n)) (x i : Fin n) (hx : x ∉ s) :
    mark s x i = 1 ↔ i = x := by
  by_cases e : i = x
  · subst i; simp [mark,hx]
  · by_cases m : i ∈ s <;> simp [mark,m,e]

private theorem charge_on_chain (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s)
    (l : List (Fin n)) (hs : l.Pairwise (· > ·)) :
    (chain (l.map (mark s x))).2.count 1 =
    if x ∈ l then insertionCharge (l.filter (· < x)).length
      (l.filter (fun i => decide (i < x ∧ i ∈ s))).length else 0 := by
  induction l with
  | nil => simp [chain]
  | cons y ys ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp hs
    by_cases eq : y = x
    · subst y
      have nf : x ∉ ys := fun h => lt_irrefl _ (head x h)
      have f₁ : ys.filter (· < x) = ys := List.filter_eq_self.mpr (fun i hi => by simpa using head i hi)
      have f₂ : ys.filter (fun i => decide (i < x ∧ i ∈ s)) = ys.filter (· ∈ s) := by
        apply List.filter_congr
        intro i hi
        simp [head i hi]
      have f₃ : ((ys.map (mark s x)).filter (· ≤ 1)).length = (ys.filter (· ∈ s)).length := by
        rw [List.filter_map,List.length_map]
        congr 1
        apply List.filter_congr
        intro i hi
        have hne : i ≠ x := fun e => nf (e ▸ hi)
        by_cases mem : i ∈ s <;> simp [Function.comp_def,mark,mem,hne]
      simp [chain,List.count_append, ih tail, nf, mark_is_one, mark, hx, ins_on_prefix,
        f₁,f₂, f₃]
      simp only [Bool.decide_and] at f₂
      rw [f₂]
    · have ne : mark s x y ≠ 1 := fun he => eq ((mark_is_one s x y hx).mp he)
      by_cases mem : x ∈ ys
      · have hgt := head x mem
        simp [chain, List.count_replicate, ne, ih tail, mem, not_lt_of_gt hgt]
      · simp [chain, List.count_replicate, ne, ih tail, mem, Ne.symm eq]

theorem pass_charge (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) (hh : 0 < h) :
    (passTrace (mark s x) h).count 1 =
      insertionCharge (x.val/h) (earlierSmall n h s x.val) := by
  let r := x.val%h
  have hv (a : Nat) : (bucket (mark s x) h a).2.count 1 =
      if a = r then insertionCharge (x.val/h) (earlierSmall n h s x.val) else 0 := by
    have hs : (slots n h a).reverse.Pairwise (· > ·) := by
      rw [List.pairwise_reverse]
      exact (List.pairwise_lt_finRange n).sublist List.filter_sublist
    have hm : x ∈ (slots n h a).reverse ↔ x.val%h = a := by simp [slots]
    rw [bucket, ← List.map_reverse, charge_on_chain s x hx _ hs]
    by_cases e : a = r
    · subst a
      have hc := count_before (h := h) s x
      simp only [Bool.decide_and] at hc
      simp [hm,r,slots_earlier x hh,hc]
    · simp [hm,r] at e ⊢
      simp [e,Ne.symm e]
  simp only [passTrace,List.count_flatMap,Function.comp_def,hv]
  rw [List.sum_map_eq_nsmul_single r]
  · simp [r, List.count_eq_of_nodup List.nodup_range, Nat.mod_lt _ hh]
  · intro a ne _
    simp [ne]

theorem weight_eq (gaps : List Nat) (hg : ∀ h ∈ gaps, 0 < h)
    (s : Finset (Fin n)) (x : Fin n) (hx : x ∉ s) :
    markedWeight gaps s x = edgeWeight n gaps s x.val := by
  induction gaps generalizing s x with
  | nil => rfl
  | cons h hs ih =>
    have hh := hg h (by simp)
    have ht : ∀ j ∈ hs, 0 < j := fun j hj => hg j (by simp [hj])
    simp only [markedWeight, trace, List.count_append, pass_charge s x hx hh, pass_mark s x hx hh,
      edgeWeight]
    exact congrArg (_ + ·) (ih ht _ _ (transported_fresh s x hx hh))

theorem walk_weight_eq (gaps : List Nat) (hg : ∀ h ∈ gaps, 0 < h)
    {k : Nat} {s : Finset (Fin n)} {xs : List (Fin n)}
    (hw : Walk (unused n) (addPosition n) k s xs) :
    walkCost (addPosition n) (markedWeight gaps) s xs =
    walkCost (addPosition n) (fun t (i : Fin n) => edgeWeight n gaps t i.val) s xs := by
  induction hw with
  | nil => rfl
  | @cons k s x xs hx ht ih =>
    simp only [walkCost, weight_eq gaps hg s x ((unused_spec n s x).mp hx), ih]

theorem actual_threshold_path (P : Equiv.Perm (Fin n)) (gaps : List Nat)
    (hg : ∀ h ∈ gaps, 0 < h) :
    (trace (fun i => P i) gaps).length =
      walkCost (addPosition n) (fun t (i : Fin n) => edgeWeight n gaps t i.val) ∅ (positions P) :=
  (shell_path P gaps).symm.trans (walk_weight_eq gaps hg (positions_walk P))

theorem actual_threshold_maximum (gaps : List Nat) (hg : ∀ h ∈ gaps, 0 < h) :
    (∀ P : Equiv.Perm (Fin n), (trace (fun i => P i) gaps).length ≤ thresholdMaximum n gaps) ∧
    ∃ P : Equiv.Perm (Fin n), (trace (fun i => P i) gaps).length = thresholdMaximum n gaps := by
  obtain ⟨upper, xs, hw, he⟩ := thresholdMaximum_exact n gaps
  constructor
  · intro P
    exact (actual_threshold_path P gaps hg).trans_le (upper _ (positions_walk P))
  · obtain ⟨P, hp, _⟩ := permutation_of_walk hw
    exact ⟨P, (actual_threshold_path P gaps hg).trans (hp ▸ he)⟩

end ShellMinimax
