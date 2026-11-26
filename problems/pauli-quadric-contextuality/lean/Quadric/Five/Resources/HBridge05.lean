import Quadric.Five.Resources.HPacket05
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket05
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover160 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 160 Quadric.Five.Census.LevelOne.chunk5) :=
  certify_packet records160 (by decide +kernel) accepted160
end Quadric.Five.Moves.HPacket05
