import Quadric.Five.Resources.HPacket07
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket07
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover224 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 224 Quadric.Five.Census.LevelOne.chunk7) :=
  certify_packet records224 (by decide +kernel) accepted224
end Quadric.Five.Moves.HPacket07
