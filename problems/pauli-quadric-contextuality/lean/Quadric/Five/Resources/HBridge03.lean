import Quadric.Five.Resources.HPacket03
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket03
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover96 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 96 Quadric.Five.Census.LevelOne.chunk3) :=
  certify_packet records96 (by decide +kernel) accepted96
end Quadric.Five.Moves.HPacket03
