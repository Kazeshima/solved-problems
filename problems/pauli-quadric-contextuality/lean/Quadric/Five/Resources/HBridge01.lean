import Quadric.Five.Resources.HPacket01
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Moves.HPacket01
open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
set_option Elab.async false
theorem cover32 : CertifiedList true hProfiles (firstCodes Quadric.Five.Census.LevelOne.freePoints 32 Quadric.Five.Census.LevelOne.chunk1) :=
  certify_packet records32 (by decide +kernel) accepted32
end Quadric.Five.Moves.HPacket01
