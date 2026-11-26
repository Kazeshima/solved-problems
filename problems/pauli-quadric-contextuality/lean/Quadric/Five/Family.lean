import Quadric.Five.Packets
import Quadric.Five.TailNormal
import Quadric.Five.Resources.ProfileMasks

namespace Quadric.Five.Moves
open Census Data
def ProfileCase (rep : ℕ) : Prop := ∃ rows : List Block.Row, ∃ len : rows.length=2048,
  CompleteBlock rep rows len ∧ CertifiedList false fullProfiles (secondCodes tailFree rep 0 rows)

theorem jointFirst {targets free : List ℕ} {h n : ℕ} {l r : List (List ℕ)} (len : l.length=n)
    (p : CertifiedList true targets (firstCodes free h l))
    (q : CertifiedList true targets (firstCodes free (h+n) r)) :
    CertifiedList true targets (firstCodes free h (l++r)) := by
  rw [first_append,len]; exact p.join q

theorem jointSecond {targets free : List ℕ} {rep h n : ℕ} {l r : List Block.Row} (len : l.length=n)
    (p : CertifiedList false targets (secondCodes free rep h l))
    (q : CertifiedList false targets (secondCodes free rep (h+n) r)) :
    CertifiedList false targets (secondCodes free rep h (l++r)) := by
  rw [second_append,len]; exact p.join q

end Quadric.Five.Moves
