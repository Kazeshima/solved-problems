import Quadric.Five.Resources.Cert00
import Quadric.Five.Resources.Cert01
import Quadric.Five.Resources.Cert02
import Quadric.Five.Resources.Cert03
import Quadric.Five.Resources.Cert04
import Quadric.Five.Resources.Cert05
import Quadric.Five.Resources.Cert06
import Quadric.Five.Resources.Cert07
import Quadric.Five.Resources.Cert08
import Quadric.Five.Resources.Cert09
import Quadric.Five.Resources.Cert10
import Quadric.Five.Resources.Cert11
import Quadric.Five.Resources.Cert12
import Quadric.Five.Resources.Cert13
import Quadric.Five.Resources.Cert14
import Quadric.Five.Resources.Cert15
import Quadric.Five.Resources.Cert16
import Quadric.Five.Resources.Cert17
import Quadric.Five.Resources.Cert18
import Quadric.Five.Resources.Cert19
import Quadric.Five.Resources.Cert20
import Quadric.Five.Resources.Cert21
import Quadric.Five.Resources.Cert22
import Quadric.Five.Resources.Cert23
import Quadric.Five.Resources.Cert24
import Quadric.Five.Resources.Cert25
import Quadric.Five.Resources.Cert26
import Quadric.Five.Resources.Cert27
import Quadric.Five.Resources.Cert28
import Quadric.Five.Resources.Cert29
import Quadric.Five.Resources.Cert30
import Quadric.Five.Resources.Cert31
import Quadric.Five.Resources.Cert32
import Quadric.Five.Resources.Cert33
import Quadric.Five.Resources.Cert34
import Quadric.Five.Resources.Cert35
import Quadric.Five.Resources.Cert36
import Quadric.Five.Resources.Cert37
import Quadric.Five.Resources.Cert38
import Quadric.Five.Resources.Cert39
import Quadric.Five.Resources.Cert40
import Quadric.Five.Resources.Cert41

namespace Quadric.Five.Certificates
open Small Data

def ProfileBound (sigma : ℕ) :=
  ∀ s : ℕ→Bool, 315≤errors full3 sigma.testBit + outsideErrors sigma s

noncomputable def sigmas : List ℕ :=
  [cert00.sigma, cert01.sigma, cert02.sigma, cert03.sigma, cert04.sigma, cert05.sigma, cert06.sigma, cert07.sigma, cert08.sigma, cert09.sigma, cert10.sigma, cert11.sigma, cert12.sigma, cert13.sigma, cert14.sigma, cert15.sigma, cert16.sigma, cert17.sigma, cert18.sigma, cert19.sigma, cert20.sigma, cert21.sigma, cert22.sigma, cert23.sigma, cert24.sigma, cert25.sigma, cert26.sigma, cert27.sigma, cert28.sigma, cert29.sigma, cert30.sigma, cert31.sigma, cert32.sigma, cert33.sigma, cert34.sigma, cert35.sigma, cert36.sigma, cert37.sigma, cert38.sigma, cert39.sigma, cert40.sigma, cert41.sigma]

private def Bounds : List ℕ→Prop
  | []=>True
  | x::xs=>ProfileBound x ∧ Bounds xs

private theorem of_bounds {xs : List ℕ} (h : Bounds xs) {x : ℕ} (hx : x∈xs) : ProfileBound x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · exact h.1
    · exact ih h.2 hx

private theorem checked : Bounds sigmas :=
  ⟨bound00, bound01, bound02, bound03, bound04, bound05, bound06, bound07, bound08, bound09, bound10, bound11, bound12, bound13, bound14, bound15, bound16, bound17, bound18, bound19, bound20, bound21, bound22, bound23, bound24, bound25, bound26, bound27, bound28, bound29, bound30, bound31, bound32, bound33, bound34, bound35, bound36, bound37, bound38, bound39, bound40, bound41, trivial⟩

theorem all_42_certificates {sigma : ℕ} (hs : sigma∈sigmas) : ProfileBound sigma :=
  of_bounds checked hs

theorem distinct_42 : sigmas.length=42 ∧ sigmas.Nodup := by decide +kernel

end Quadric.Five.Certificates
