import Quadric.Five.Screen

namespace Quadric.Five.Census
open Packing
set_option maxRecDepth 4096
set_option maxHeartbeats 900000

structure Prepared (S : Split) : Prop where
  wa : S.first.lowWidth=8
  wb : S.second.lowWidth=8
  wc : S.crossBlock.lowWidth=8
  la : S.lowFirst.length=256
  lb : S.lowSecond.length=256
  threshold : S.cutoff<512
  budget : S.high.length + size S.first + size S.second + size S.crossBlock ≤ 511
  minA (a b : ℕ) (ha : a<256) (hb : b<256) :
    crossMinimumA S a ≤ errorCount S.crossBlock a b
  minB (a b : ℕ) (ha : a<256) (hb : b<256) :
    crossMinimumB S b ≤ errorCount S.crossBlock a b

private theorem uniform_pack (k c : ℕ) : c*ones k=pack (2^k) (fun _=>c) := by
  rw [ones_eq,←pack_mul]; simp

private theorem from_list_bound (l : List ℕ) (h : l.all (·≤511)=true) (j : ℕ) (hj : j<l.length) :
    l[j]?.getD 0 ≤ 512 := by
  rw [List.getElem?_eq_getElem hj]; simp only [Option.getD_some]
  have := of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hj)); omega

theorem prepare_sound (S : Split) (ok : prepOK S=true) : Prepared S := by
  obtain ⟨bounds,checks⟩ := Bool.and_eq_true_iff.mp ok
  simp only [Bool.and_eq_true_iff,beq_iff_eq,decide_eq_true_eq] at bounds
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨wa,wb⟩,wc⟩,la⟩,lb⟩,ht⟩,budget⟩,sa⟩,sb⟩ := bounds
  have limit (a b : ℕ) : errorCount S.crossBlock a b<512 := by have := bounded S.crossBlock a b; omega
  refine ⟨wa,wb,wc,la,lb,ht,budget,?_,?_⟩
  · intro a b ha hb
    have h := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checks a (List.mem_range.mpr ha))).1
    change packedLE 8 (crossMinimumA S a*ones 8) (vector S.crossBlock a)=true at h
    rw [uniform_pack,vector_eq,wc] at h
    exact packedLE_sound (fun _ _=>from_list_bound _ sa _ (la ▸ ha)) (fun j _=>limit a j) h hb
  · intro a b ha hb
    have h := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checks a (List.mem_range.mpr ha))).2
    change packedLE 8 (packList S.lowSecond) (vector S.crossBlock a)=true at h
    rw [packList_eq,lb,vector_eq,wc] at h
    exact packedLE_sound (fun j hj=>from_list_bound _ sb j (by simpa only [lb] using hj))
      (fun j _=>limit a j) h hb

attribute [local irreducible] pack winnersMask declaredMask

private theorem mask_iff {f : ℕ→ℕ} {T : ℕ} (lim : ∀i<256,f i≤512) (ht : T<512)
    {xs : List ℕ} (h : winnersMask 8 T (pack 256 f)=declaredMask xs) {i} (hi : i<256) :
    f i≤T ↔ i∈xs := by
  have eq := congrArg (fun v:ℕ=>v.testBit (10*i+9)) h
  have left := winner_bit 8 T f lim ht i hi
  rw [show (2:ℕ)^8=256 by decide] at left
  have tag := left.symm.trans (eq.trans (declared_bit xs i))
  constructor
  · intro h; exact of_decide_eq_true (tag ▸ decide_eq_true h)
  · intro h; exact of_decide_eq_true (tag.symm ▸ decide_eq_true h)

private theorem projected (s : System) (hw : s.lowWidth=8) (h : ℕ) (xs : List ℕ)
    (len : xs.length=256) (base : ℕ) :
    vector s h+packList xs+base*ones 8 =
      pack 256 (fun i=>errorCount s h i+xs[i]?.getD 0+base) := by
  rw [vector_eq,hw,packList_eq,len,uniform_pack,show (2:ℕ)^8=256 by decide]
  rw [pack_add,pack_add]

theorem screened_iff (S : Split) (ready : Prepared S) (h a b : ℕ) (ha : a<256) (hb : b<256)
    (r : Row) (ok : rowPass S h r=true) :
    fullCost S h a b ≤ S.cutoff ↔ a+256*b∈r.hits := by
  have bud:=ready.budget
  have bh : highOnly S h ≤ S.high.length := List.countP_le_length
  have full (i j) : fullCost S h i j≤511 := by
    unfold fullCost; have := bounded S.first h i; have := bounded S.second h j
    have := bounded S.crossBlock i j; omega
  simp only [rowPass,Bool.and_eq_true_iff,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨mA,mB⟩,loA⟩,loB⟩,ma⟩,mb⟩,candidate⟩,wins⟩ := ok
  rw [uniform_pack,vector_eq,ready.wa] at loA
  rw [uniform_pack,vector_eq,ready.wb] at loB
  have lowerA (i) (hi : i<256) : r.minA ≤ errorCount S.first h i :=
    packedLE_sound (fun _ _=>by omega) (fun j _=>by have := bounded S.first h j; omega) loA hi
  have lowerB (i) (hi : i<256) : r.minB ≤ errorCount S.second h i :=
    packedLE_sound (fun _ _=>by omega) (fun j _=>by have := bounded S.second h j; omega) loB hi
  let pa (i : ℕ) := errorCount S.first h i+crossMinimumA S i+(highOnly S h+r.minB)
  let pb (j : ℕ) := errorCount S.second h j+crossMinimumB S j+(highOnly S h+r.minA)
  have pA (i j) (hi : i<256) (hj : j<256) : pa i ≤ fullCost S h i j := by
    dsimp [pa,fullCost]; have := ready.minA i j hi hj; have := lowerB j hj; omega
  have pB (i j) (hi : i<256) (hj : j<256) : pb j ≤ fullCost S h i j := by
    dsimp [pb,fullCost]; have := ready.minB i j hi hj; have := lowerA i hi; omega
  rw [projected S.first ready.wa _ _ ready.la] at ma
  rw [projected S.second ready.wb _ _ ready.lb] at mb
  change winnersMask 8 S.cutoff (pack 256 pa)=_ at ma
  change winnersMask 8 S.cutoff (pack 256 pb)=_ at mb
  have Va : digit (vector S.first h) a=errorCount S.first h a := by
    rw [vector_eq,ready.wa]; exact digit_pack _ _ (fun j _=>by have := bounded S.first h j; omega) _ ha
  have Vb : digit (vector S.second h) b=errorCount S.second h b := by
    rw [vector_eq,ready.wb]; exact digit_pack _ _ (fun j _=>by have := bounded S.second h j; omega) _ hb
  have Vc : digit (vector S.crossBlock a) b=errorCount S.crossBlock a b := by
    rw [vector_eq,ready.wc]; exact digit_pack _ _ (fun j _=>by have := bounded S.crossBlock a j; omega) _ hb
  constructor
  · intro hs
    have ia := (mask_iff (fun i hi => by have := pA i 0 hi (by decide); have := full i 0; omega)
      ready.threshold ma ha).mp ((pA a b ha hb).trans hs)
    have ib := (mask_iff (fun j hj => by have := pB 0 j (by decide) hj; have := full 0 j; omega)
      ready.threshold mb hb).mp ((pB a b ha hb).trans hs)
    have hh := List.all_eq_true.mp (List.all_eq_true.mp candidate a ia) b ib
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.contains_iff_mem,Va,Vb,Vc] at hh
    exact hh.resolve_left (Nat.not_lt.mpr hs)
  · intro hin
    have hh := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp wins _ hin)).2
    have md : (a+256*b)%256=a := by omega
    have dv : (a+256*b)/256=b := by omega
    simpa only [md,dv,Va,Vb,Vc,decide_eq_true_eq,fullCost] using hh

end Quadric.Five.Census
