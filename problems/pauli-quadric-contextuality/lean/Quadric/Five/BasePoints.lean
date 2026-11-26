import Quadric.Five.Transport

namespace Quadric.Five

def ellipticBase : Label 4 := pole 3
def sectionBase : Label 4 := (Fin.cons 1 0,0)
theorem elliptic_type : q ellipticBase=1 := pole_q _
theorem sectionBase_off : form ellipticBase sectionBase=1 := by
  simp [ellipticBase,sectionBase,pole,form,q,polar,cross,dot_cons]

end Quadric.Five
