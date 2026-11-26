import Quadric.Five.Resources.CloseCase00
import Quadric.Five.Resources.CloseCase01
import Quadric.Five.Resources.CloseCase02
import Quadric.Five.Resources.CloseCase03
import Quadric.Five.Resources.CloseCase04
import Quadric.Five.Resources.CloseCase05
import Quadric.Five.Resources.CloseCase06
import Quadric.Five.Resources.CloseCase07
import Quadric.Five.Resources.CloseCase08
import Quadric.Five.Resources.CloseCase09
import Quadric.Five.Resources.CloseCase10
import Quadric.Five.Resources.CloseCase11
import Quadric.Five.Resources.CloseCase12
import Quadric.Five.Resources.CloseCase13
import Quadric.Five.Resources.CloseCase14
import Quadric.Five.Resources.CloseCase15
import Quadric.Five.Resources.CloseCase16
import Quadric.Five.Resources.CloseCase17
namespace Quadric.Five.Moves.Data
open Census
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
set_option Elab.async false
private def AllProfiles : List ℕ→Prop | []=>True | x::xs=>ProfileCase x ∧ AllProfiles xs
private theorem all_profiles : AllProfiles hProfiles :=
  ⟨Block.Case00.profile_case, Block.Case01.profile_case, Block.Case02.profile_case, Block.Case03.profile_case, Block.Case04.profile_case, Block.Case05.profile_case, Block.Case06.profile_case, Block.Case07.profile_case, Block.Case08.profile_case, Block.Case09.profile_case, Block.Case10.profile_case, Block.Case11.profile_case, Block.Case12.profile_case, Block.Case13.profile_case, Block.Case14.profile_case, Block.Case15.profile_case, Block.Case16.profile_case, Block.Case17.profile_case, trivial⟩
theorem complete_cases : ∀x∈hProfiles,ProfileCase x := by
  have elim (xs : List ℕ) (h : AllProfiles xs) : ∀ x∈xs,ProfileCase x := by
    induction xs with
    | nil => simp
    | cons a xs ih => intro x hx; rcases List.mem_cons.mp hx with rfl|hz; exact h.1; exact ih h.2 x hz
  exact elim _ all_profiles
end Quadric.Five.Moves.Data
