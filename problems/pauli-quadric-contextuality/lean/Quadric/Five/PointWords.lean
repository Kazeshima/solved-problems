import Quadric.Five.Paths
import Quadric.Five.Hyperplanes
import Quadric.Five.SortWitness

namespace Quadric.Five.Moves
open Small

def backLine (table : List Move) : List ℕ→Line→Line
  | [],l=>l
  | i::is,l=>
    let rest:=backLine table is l
    match table[i]? with
    | none=>rest
    | some m=>relabel m rest

theorem failure_word (table : List Move) (w : List ℕ) (s : ℕ→Bool) (l : Line) :
    Small.failure (action table w s) l=Small.failure s (backLine table w l) := by
  induction w generalizing s with
  | nil => rfl
  | cons i is ih =>
    cases he:table[i]? <;> simp only [action,backLine,he,ih,failure_pull]

def equalCatalogues (l r : List Line) := decide (orderFuel 11 l=orderFuel 11 r)

theorem perm_of_catalogues {l r : List Line} (h : equalCatalogues l r=true) : l.Perm r := by
  have p:=(order_perm 11 l).symm
  rw [of_decide_eq_true h] at p
  exact p.trans (order_perm ..)

def hyperLines (u : ℕ) := full3.filter (inHyperplane u)

theorem fix_section (table : List Move) (w : List ℕ) (u : ℕ) (s : ℕ→Bool)
    (h : equalCatalogues ((hyperLines 36).map (backLine table w)) (hyperLines u)=true) :
    hyperErrors (action table w s) 36=hyperErrors s u := by
  have eq:=(perm_of_catalogues h).countP_eq (Small.failure s)
  simpa only [hyperErrors,hyperLines,errors,List.countP_map,Function.comp_def,←failure_word] using eq

end Quadric.Five.Moves
