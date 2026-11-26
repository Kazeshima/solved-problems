import Quadric.Five.Packets

namespace Quadric.Five.Moves
open Census

theorem certify_slice {targets ids : List ℕ} (ws : List Witness) (offset size : ℕ)
    (eq : (((ws.drop offset).take size).map Witness.start)=ids)
    (valid : ws.all (validRecord false targets)=true) : CertifiedList false targets ids := by
  apply certify_packet _ eq
  apply List.all_eq_true.mpr
  intro w hw
  exact List.all_eq_true.mp valid _ (List.mem_of_mem_drop (List.mem_of_mem_take hw))

def RowCoverage (targets free : List ℕ) (rep : ℕ) : ℕ → List Block.Row → Prop
  | _,[] => True
  | h,r::rs => CertifiedList false targets (codeRow free rep h r) ∧ RowCoverage targets free rep (h+1) rs

theorem row_coverage_sound {targets free : List ℕ} {rep h : ℕ} {rs : List Block.Row}
    (p : RowCoverage targets free rep h rs) : CertifiedList false targets (secondCodes free rep h rs) := by
  induction rs generalizing h with
  | nil => intro x hx; simp [secondCodes] at hx
  | cons r rs ih => exact p.1.join (ih p.2)

end Quadric.Five.Moves
