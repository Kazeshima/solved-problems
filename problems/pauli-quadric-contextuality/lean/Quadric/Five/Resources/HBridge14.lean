import Quadric.Five.Resources.HPacket14
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket14
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover448 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 448 Quadric.Five.Census.LevelOne.chunk14) :=
  certify_packet records448 (by decide +kernel) accepted448
end Quadric.Five.Moves.HPacket14
