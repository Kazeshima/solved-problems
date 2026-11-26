import Quadric.Five.Resources.HPacket00
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket00
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover0 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 0 Quadric.Five.Census.LevelOne.chunk0) :=
  certify_packet records0 (by decide +kernel) accepted0
end Quadric.Five.Moves.HPacket00
