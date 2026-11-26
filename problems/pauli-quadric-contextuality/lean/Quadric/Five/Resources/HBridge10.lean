import Quadric.Five.Resources.HPacket10
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket10
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover320 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 320 Quadric.Five.Census.LevelOne.chunk10) :=
  certify_packet records320 (by decide +kernel) accepted320
end Quadric.Five.Moves.HPacket10
