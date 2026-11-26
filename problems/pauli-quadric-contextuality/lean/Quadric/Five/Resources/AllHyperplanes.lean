import Quadric.Five.Family
import Quadric.Five.Resources.HBridge00
import Quadric.Five.Resources.HBridge01
import Quadric.Five.Resources.HBridge02
import Quadric.Five.Resources.HBridge03
import Quadric.Five.Resources.HBridge04
import Quadric.Five.Resources.HBridge05
import Quadric.Five.Resources.HBridge06
import Quadric.Five.Resources.HBridge07
import Quadric.Five.Resources.HBridge08
import Quadric.Five.Resources.HBridge09
import Quadric.Five.Resources.HBridge10
import Quadric.Five.Resources.HBridge11
import Quadric.Five.Resources.HBridge12
import Quadric.Five.Resources.HBridge13
import Quadric.Five.Resources.HBridge14
import Quadric.Five.Resources.HBridge15
namespace Quadric.Five.Moves.Data
open Census
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
set_option Elab.async false
private noncomputable def tail15 := LevelOne.chunk15
private theorem accepted15 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 480 tail15) :=
  HPacket15.cover480
private noncomputable def tail14 := LevelOne.chunk14 ++ tail15
private theorem accepted14 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 448 tail14) :=
  @jointFirst hProfiles LevelOne.freePoints 448 32 LevelOne.chunk14 tail15 (by decide +kernel) HPacket14.cover448 accepted15
private noncomputable def tail13 := LevelOne.chunk13 ++ tail14
private theorem accepted13 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 416 tail13) :=
  @jointFirst hProfiles LevelOne.freePoints 416 32 LevelOne.chunk13 tail14 (by decide +kernel) HPacket13.cover416 accepted14
private noncomputable def tail12 := LevelOne.chunk12 ++ tail13
private theorem accepted12 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 384 tail12) :=
  @jointFirst hProfiles LevelOne.freePoints 384 32 LevelOne.chunk12 tail13 (by decide +kernel) HPacket12.cover384 accepted13
private noncomputable def tail11 := LevelOne.chunk11 ++ tail12
private theorem accepted11 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 352 tail11) :=
  @jointFirst hProfiles LevelOne.freePoints 352 32 LevelOne.chunk11 tail12 (by decide +kernel) HPacket11.cover352 accepted12
private noncomputable def tail10 := LevelOne.chunk10 ++ tail11
private theorem accepted10 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 320 tail10) :=
  @jointFirst hProfiles LevelOne.freePoints 320 32 LevelOne.chunk10 tail11 (by decide +kernel) HPacket10.cover320 accepted11
private noncomputable def tail9 := LevelOne.chunk9 ++ tail10
private theorem accepted9 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 288 tail9) :=
  @jointFirst hProfiles LevelOne.freePoints 288 32 LevelOne.chunk9 tail10 (by decide +kernel) HPacket09.cover288 accepted10
private noncomputable def tail8 := LevelOne.chunk8 ++ tail9
private theorem accepted8 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 256 tail8) :=
  @jointFirst hProfiles LevelOne.freePoints 256 32 LevelOne.chunk8 tail9 (by decide +kernel) HPacket08.cover256 accepted9
private noncomputable def tail7 := LevelOne.chunk7 ++ tail8
private theorem accepted7 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 224 tail7) :=
  @jointFirst hProfiles LevelOne.freePoints 224 32 LevelOne.chunk7 tail8 (by decide +kernel) HPacket07.cover224 accepted8
private noncomputable def tail6 := LevelOne.chunk6 ++ tail7
private theorem accepted6 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 192 tail6) :=
  @jointFirst hProfiles LevelOne.freePoints 192 32 LevelOne.chunk6 tail7 (by decide +kernel) HPacket06.cover192 accepted7
private noncomputable def tail5 := LevelOne.chunk5 ++ tail6
private theorem accepted5 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 160 tail5) :=
  @jointFirst hProfiles LevelOne.freePoints 160 32 LevelOne.chunk5 tail6 (by decide +kernel) HPacket05.cover160 accepted6
private noncomputable def tail4 := LevelOne.chunk4 ++ tail5
private theorem accepted4 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 128 tail4) :=
  @jointFirst hProfiles LevelOne.freePoints 128 32 LevelOne.chunk4 tail5 (by decide +kernel) HPacket04.cover128 accepted5
private noncomputable def tail3 := LevelOne.chunk3 ++ tail4
private theorem accepted3 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 96 tail3) :=
  @jointFirst hProfiles LevelOne.freePoints 96 32 LevelOne.chunk3 tail4 (by decide +kernel) HPacket03.cover96 accepted4
private noncomputable def tail2 := LevelOne.chunk2 ++ tail3
private theorem accepted2 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 64 tail2) :=
  @jointFirst hProfiles LevelOne.freePoints 64 32 LevelOne.chunk2 tail3 (by decide +kernel) HPacket02.cover64 accepted3
private noncomputable def tail1 := LevelOne.chunk1 ++ tail2
private theorem accepted1 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 32 tail1) :=
  @jointFirst hProfiles LevelOne.freePoints 32 32 LevelOne.chunk1 tail2 (by decide +kernel) HPacket01.cover32 accepted2
private noncomputable def tail0 := LevelOne.chunk0 ++ tail1
private theorem accepted0 : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 0 tail0) :=
  @jointFirst hProfiles LevelOne.freePoints 0 32 LevelOne.chunk0 tail1 (by decide +kernel) HPacket00.cover0 accepted1
theorem hyperplane_census : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 0 LevelOne.survivors) := accepted0
end Quadric.Five.Moves.Data
