import Quadric.Five.Resources.HPacket15
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket15
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover480 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 480 Quadric.Five.Census.LevelOne.chunk15) :=
  certify_packet records480 (by decide +kernel) accepted480
end Quadric.Five.Moves.HPacket15
