import Quadric.Five.Resources.HPacket11
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket11
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover352 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 352 Quadric.Five.Census.LevelOne.chunk11) :=
  certify_packet records352 (by decide +kernel) accepted352
end Quadric.Five.Moves.HPacket11
