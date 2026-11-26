import Quadric.Five.Resources.HPacket04
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket04
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover128 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 128 Quadric.Five.Census.LevelOne.chunk4) :=
  certify_packet records128 (by decide +kernel) accepted128
end Quadric.Five.Moves.HPacket04
