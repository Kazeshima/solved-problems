import Quadric.Five.Resources.HPacket12
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket12
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover384 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 384 Quadric.Five.Census.LevelOne.chunk12) :=
  certify_packet records384 (by decide +kernel) accepted384
end Quadric.Five.Moves.HPacket12
