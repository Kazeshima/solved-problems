import Quadric.Five.OneBlock
import Mathlib.Data.Finset.Card

namespace Quadric.Five.Census
theorem sum_join (xs ys : List ℕ) : (xs++ys).sum=xs.sum+ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih,Nat.add_assoc]

def after (p : ℕ) : List ℕ→Bool
  | []=>true
  | a::xs=>decide (p<a) && after a xs
def ascending : List ℕ→Bool
  | []=>true
  | a::xs=>after a xs

private theorem after_sound (p : ℕ) (xs : List ℕ) (h : after p xs=true) :
    xs.Pairwise (·<·) ∧ ∀a∈xs,p<a := by
  induction xs generalizing p with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨pa,hs⟩:=Bool.and_eq_true_iff.mp h
    obtain ⟨ord,gt⟩:=ih a hs
    exact ⟨List.pairwise_cons.mpr ⟨gt,ord⟩,fun b hb=>by
      rcases List.mem_cons.mp hb with rfl|hb
      · exact of_decide_eq_true pa
      · exact (of_decide_eq_true pa).trans (gt b hb)⟩

def uniqueBelow (bound : ℕ) (xs : List ℕ) := ascending xs && xs.all (·<bound)
theorem unique_sound {n} {xs : List ℕ} (h : uniqueBelow n xs=true) :
    xs.Nodup ∧ ∀i∈xs,i<n := by
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp h
  refine ⟨?_,fun i hi=>of_decide_eq_true (List.all_eq_true.mp b i hi)⟩
  cases xs with
  | nil => simp
  | cons y ys =>
    have ⟨ord,gt⟩:=after_sound y ys a
    exact (List.pairwise_cons.mpr ⟨gt,ord⟩).imp (fun h=>Nat.ne_of_lt h)

theorem count_distinct {rows : List (List ℕ)} {n} (ok : rows.all (uniqueBelow n)=true) :
    (rows.map (fun r=>r.toFinset.card)).sum=(rows.map List.length).sum := by
  congr 1; apply List.map_congr_left; intro r hr
  exact List.toFinset_card_of_nodup (unique_sound (List.all_eq_true.mp ok r hr)).1

def blockUnique (r : Block.Row) := uniqueBelow 1024 (r.slices.map Prod.fst) &&
  r.slices.all (fun v=>uniqueBelow 1024 v.2)
def rowCount (r : Block.Row) := (r.slices.map (fun v=>v.2.length)).sum
def distinctRowCount (r : Block.Row) := (r.slices.map (fun v=>v.2.toFinset.card)).sum

theorem row_distinct {r : Block.Row} (ok : blockUnique r=true) :
    (r.slices.map Prod.fst).Nodup ∧ distinctRowCount r=rowCount r := by
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp ok
  refine ⟨(unique_sound a).1,?_⟩
  unfold distinctRowCount rowCount
  congr 1; apply List.map_congr_left; intro v hv
  exact List.toFinset_card_of_nodup (unique_sound (List.all_eq_true.mp b v hv)).1

end Quadric.Five.Census
