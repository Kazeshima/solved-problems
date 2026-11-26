import Quadric.Five.Resources.HPacket02
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket02
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover64 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 64 Quadric.Five.Census.LevelOne.chunk2) :=
  certify_packet records64 (by decide +kernel) accepted64
end Quadric.Five.Moves.HPacket02
