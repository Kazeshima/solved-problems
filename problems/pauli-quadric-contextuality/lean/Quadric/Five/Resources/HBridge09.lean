import Quadric.Five.Resources.HPacket09
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket09
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover288 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 288 Quadric.Five.Census.LevelOne.chunk9) :=
  certify_packet records288 (by decide +kernel) accepted288
end Quadric.Five.Moves.HPacket09
