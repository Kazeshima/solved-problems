import Quadric.Five.Resources.Symmetry00
import Quadric.Five.Resources.Symmetry01
import Quadric.Five.Resources.Symmetry02
import Quadric.Five.Resources.Symmetry03
import Quadric.Five.Resources.Symmetry04
import Quadric.Five.Resources.Symmetry05
import Quadric.Five.Resources.Symmetry06
import Quadric.Five.Resources.Symmetry07
import Quadric.Five.Resources.Symmetry08
import Quadric.Five.Resources.Symmetry09
import Quadric.Five.Resources.Symmetry10
import Quadric.Five.Resources.Symmetry11

namespace Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option Elab.async false
theorem all_good : ∀ m∈table,Good m := by
  have all : table.all checkGeometry=true := by
    simp only [table,List.all_cons,List.all_nil,geometry0,geometry1,geometry2,geometry3,geometry4,geometry5,geometry6,geometry7,geometry8,geometry9,geometry10,geometry11,geometry12,geometry13,geometry14,geometry15,geometry16,geometry17,geometry18,geometry19,geometry20,geometry21,geometry22,geometry23,geometry24,geometry25,geometry26,geometry27,geometry28,geometry29,geometry30,geometry31,geometry32,geometry33,geometry34,geometry35,geometry36,geometry37,geometry38,geometry39,geometry40,geometry41,geometry42,geometry43,geometry44,geometry45,geometry46,geometry47,geometry48,geometry49,geometry50,geometry51,geometry52,geometry53,geometry54,geometry55,geometry56,geometry57,geometry58,geometry59,geometry60,geometry61,geometry62,geometry63,geometry64,geometry65,geometry66,geometry67,geometry68,geometry69,geometry70,geometry71,Bool.and_self]
  intro m hm; exact geometry_checked m (List.all_eq_true.mp table_routes m hm) (List.all_eq_true.mp all m hm)
end Quadric.Five.Moves.Data
