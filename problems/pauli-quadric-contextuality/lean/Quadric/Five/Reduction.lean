import Quadric.Five.SectionChain
import Quadric.Five.Tagged

namespace Quadric.Five
open Tagged Small
attribute [local irreducible] degree faults quadric slice actualDomain

/-- The remaining finite elliptic implication, expressed solely in the 119 signed tags. -/
def EllipticCompletions : Prop := ∀ s : ℕ→Bool, errors full3 s ≤ 92 → 315 ≤ errors ellipticLines s

theorem exact_of_catalogues (innerValid : (full3.flatMap six).all (lineCheck true)=true)
    (innerUnique : fresh 0 ((full3.flatMap six).map key)=true)
    (allValid : (ellipticLines.flatMap six).all (lineCheck false)=true)
    (allUnique : fresh 0 ((ellipticLines.flatMap six).map key)=true)
    (census : EllipticCompletions) : degree 5=6975 := by
  apply exact_of_elliptic_base
  apply elliptic_reduction
  intro s cheap
  have hi:=catalogue_lower true full3 s innerValid innerUnique
  have ha:=catalogue_lower false ellipticLines s allValid allUnique
  unfold actualDomain at hi ha
  simp only [Bool.false_eq_true,if_false,if_true] at hi ha
  have small : errors full3 (signing s) ≤ 92 := by omega
  have bound:=census _ small
  omega

end Quadric.Five
