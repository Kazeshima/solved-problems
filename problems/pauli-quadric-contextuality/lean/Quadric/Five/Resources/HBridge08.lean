import Quadric.Five.Resources.HPacket08
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket08
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover256 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 256 Quadric.Five.Census.LevelOne.chunk8) :=
  certify_packet records256 (by decide +kernel) accepted256
end Quadric.Five.Moves.HPacket08
