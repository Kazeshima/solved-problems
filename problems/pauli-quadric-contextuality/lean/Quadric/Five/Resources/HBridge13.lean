import Quadric.Five.Resources.HPacket13
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket13
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover416 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 416 Quadric.Five.Census.LevelOne.chunk13) :=
  certify_packet records416 (by decide +kernel) accepted416
end Quadric.Five.Moves.HPacket13
