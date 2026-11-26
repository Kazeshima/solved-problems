import Quadric.Five.Family
import Quadric.Five.Resources.CaseForms09
import Quadric.Five.Resources.RBridge09_0
import Quadric.Five.Resources.RBridge09_1
import Quadric.Five.Resources.RBridge09_2
import Quadric.Five.Resources.RBridge09_3
namespace Quadric.Five.Census.Block.Case09
open Quadric.Five.Moves Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
set_option Elab.async false
private theorem covergroup0_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_64) :=
  @jointSecond fullProfiles freePoints restriction 0 32 row0 row32 (by decide +kernel) RPacket09_0.cover0 RPacket09_0.cover32
private theorem covergroup64_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 64 group64_64) :=
  @jointSecond fullProfiles freePoints restriction 64 32 row64 row96 (by decide +kernel) RPacket09_0.cover64 RPacket09_0.cover96
private theorem covergroup128_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 128 group128_64) :=
  @jointSecond fullProfiles freePoints restriction 128 32 row128 row160 (by decide +kernel) RPacket09_0.cover128 RPacket09_0.cover160
private theorem covergroup192_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 192 group192_64) :=
  @jointSecond fullProfiles freePoints restriction 192 32 row192 row224 (by decide +kernel) RPacket09_0.cover192 RPacket09_0.cover224
private theorem covergroup256_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 256 group256_64) :=
  @jointSecond fullProfiles freePoints restriction 256 32 row256 row288 (by decide +kernel) RPacket09_0.cover256 RPacket09_0.cover288
private theorem covergroup320_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 320 group320_64) :=
  @jointSecond fullProfiles freePoints restriction 320 32 row320 row352 (by decide +kernel) RPacket09_0.cover320 RPacket09_0.cover352
private theorem covergroup384_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 384 group384_64) :=
  @jointSecond fullProfiles freePoints restriction 384 32 row384 row416 (by decide +kernel) RPacket09_0.cover384 RPacket09_0.cover416
private theorem covergroup448_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 448 group448_64) :=
  @jointSecond fullProfiles freePoints restriction 448 32 row448 row480 (by decide +kernel) RPacket09_0.cover448 RPacket09_0.cover480
private theorem covergroup512_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 512 group512_64) :=
  @jointSecond fullProfiles freePoints restriction 512 32 row512 row544 (by decide +kernel) RPacket09_1.cover512 RPacket09_1.cover544
private theorem covergroup576_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 576 group576_64) :=
  @jointSecond fullProfiles freePoints restriction 576 32 row576 row608 (by decide +kernel) RPacket09_1.cover576 RPacket09_1.cover608
private theorem covergroup640_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 640 group640_64) :=
  @jointSecond fullProfiles freePoints restriction 640 32 row640 row672 (by decide +kernel) RPacket09_1.cover640 RPacket09_1.cover672
private theorem covergroup704_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 704 group704_64) :=
  @jointSecond fullProfiles freePoints restriction 704 32 row704 row736 (by decide +kernel) RPacket09_1.cover704 RPacket09_1.cover736
private theorem covergroup768_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 768 group768_64) :=
  @jointSecond fullProfiles freePoints restriction 768 32 row768 row800 (by decide +kernel) RPacket09_1.cover768 RPacket09_1.cover800
private theorem covergroup832_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 832 group832_64) :=
  @jointSecond fullProfiles freePoints restriction 832 32 row832 row864 (by decide +kernel) RPacket09_1.cover832 RPacket09_1.cover864
private theorem covergroup896_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 896 group896_64) :=
  @jointSecond fullProfiles freePoints restriction 896 32 row896 row928 (by decide +kernel) RPacket09_1.cover896 RPacket09_1.cover928
private theorem covergroup960_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 960 group960_64) :=
  @jointSecond fullProfiles freePoints restriction 960 32 row960 row992 (by decide +kernel) RPacket09_1.cover960 RPacket09_1.cover992
private theorem covergroup1024_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1024 group1024_64) :=
  @jointSecond fullProfiles freePoints restriction 1024 32 row1024 row1056 (by decide +kernel) RPacket09_2.cover1024 RPacket09_2.cover1056
private theorem covergroup1088_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1088 group1088_64) :=
  @jointSecond fullProfiles freePoints restriction 1088 32 row1088 row1120 (by decide +kernel) RPacket09_2.cover1088 RPacket09_2.cover1120
private theorem covergroup1152_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1152 group1152_64) :=
  @jointSecond fullProfiles freePoints restriction 1152 32 row1152 row1184 (by decide +kernel) RPacket09_2.cover1152 RPacket09_2.cover1184
private theorem covergroup1216_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1216 group1216_64) :=
  @jointSecond fullProfiles freePoints restriction 1216 32 row1216 row1248 (by decide +kernel) RPacket09_2.cover1216 RPacket09_2.cover1248
private theorem covergroup1280_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1280 group1280_64) :=
  @jointSecond fullProfiles freePoints restriction 1280 32 row1280 row1312 (by decide +kernel) RPacket09_2.cover1280 RPacket09_2.cover1312
private theorem covergroup1344_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1344 group1344_64) :=
  @jointSecond fullProfiles freePoints restriction 1344 32 row1344 row1376 (by decide +kernel) RPacket09_2.cover1344 RPacket09_2.cover1376
private theorem covergroup1408_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1408 group1408_64) :=
  @jointSecond fullProfiles freePoints restriction 1408 32 row1408 row1440 (by decide +kernel) RPacket09_2.cover1408 RPacket09_2.cover1440
private theorem covergroup1472_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1472 group1472_64) :=
  @jointSecond fullProfiles freePoints restriction 1472 32 row1472 row1504 (by decide +kernel) RPacket09_2.cover1472 RPacket09_2.cover1504
private theorem covergroup1536_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1536 group1536_64) :=
  @jointSecond fullProfiles freePoints restriction 1536 32 row1536 row1568 (by decide +kernel) RPacket09_3.cover1536 RPacket09_3.cover1568
private theorem covergroup1600_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1600 group1600_64) :=
  @jointSecond fullProfiles freePoints restriction 1600 32 row1600 row1632 (by decide +kernel) RPacket09_3.cover1600 RPacket09_3.cover1632
private theorem covergroup1664_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1664 group1664_64) :=
  @jointSecond fullProfiles freePoints restriction 1664 32 row1664 row1696 (by decide +kernel) RPacket09_3.cover1664 RPacket09_3.cover1696
private theorem covergroup1728_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1728 group1728_64) :=
  @jointSecond fullProfiles freePoints restriction 1728 32 row1728 row1760 (by decide +kernel) RPacket09_3.cover1728 RPacket09_3.cover1760
private theorem covergroup1792_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1792 group1792_64) :=
  @jointSecond fullProfiles freePoints restriction 1792 32 row1792 row1824 (by decide +kernel) RPacket09_3.cover1792 RPacket09_3.cover1824
private theorem covergroup1856_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1856 group1856_64) :=
  @jointSecond fullProfiles freePoints restriction 1856 32 row1856 row1888 (by decide +kernel) RPacket09_3.cover1856 RPacket09_3.cover1888
private theorem covergroup1920_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1920 group1920_64) :=
  @jointSecond fullProfiles freePoints restriction 1920 32 row1920 row1952 (by decide +kernel) RPacket09_3.cover1920 RPacket09_3.cover1952
private theorem covergroup1984_64 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1984 group1984_64) :=
  @jointSecond fullProfiles freePoints restriction 1984 32 row1984 row2016 (by decide +kernel) RPacket09_3.cover1984 RPacket09_3.cover2016
private theorem covergroup0_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_128) :=
  @jointSecond fullProfiles freePoints restriction 0 64 group0_64 group64_64 (by decide +kernel) covergroup0_64 covergroup64_64
private theorem covergroup128_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 128 group128_128) :=
  @jointSecond fullProfiles freePoints restriction 128 64 group128_64 group192_64 (by decide +kernel) covergroup128_64 covergroup192_64
private theorem covergroup256_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 256 group256_128) :=
  @jointSecond fullProfiles freePoints restriction 256 64 group256_64 group320_64 (by decide +kernel) covergroup256_64 covergroup320_64
private theorem covergroup384_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 384 group384_128) :=
  @jointSecond fullProfiles freePoints restriction 384 64 group384_64 group448_64 (by decide +kernel) covergroup384_64 covergroup448_64
private theorem covergroup512_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 512 group512_128) :=
  @jointSecond fullProfiles freePoints restriction 512 64 group512_64 group576_64 (by decide +kernel) covergroup512_64 covergroup576_64
private theorem covergroup640_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 640 group640_128) :=
  @jointSecond fullProfiles freePoints restriction 640 64 group640_64 group704_64 (by decide +kernel) covergroup640_64 covergroup704_64
private theorem covergroup768_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 768 group768_128) :=
  @jointSecond fullProfiles freePoints restriction 768 64 group768_64 group832_64 (by decide +kernel) covergroup768_64 covergroup832_64
private theorem covergroup896_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 896 group896_128) :=
  @jointSecond fullProfiles freePoints restriction 896 64 group896_64 group960_64 (by decide +kernel) covergroup896_64 covergroup960_64
private theorem covergroup1024_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1024 group1024_128) :=
  @jointSecond fullProfiles freePoints restriction 1024 64 group1024_64 group1088_64 (by decide +kernel) covergroup1024_64 covergroup1088_64
private theorem covergroup1152_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1152 group1152_128) :=
  @jointSecond fullProfiles freePoints restriction 1152 64 group1152_64 group1216_64 (by decide +kernel) covergroup1152_64 covergroup1216_64
private theorem covergroup1280_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1280 group1280_128) :=
  @jointSecond fullProfiles freePoints restriction 1280 64 group1280_64 group1344_64 (by decide +kernel) covergroup1280_64 covergroup1344_64
private theorem covergroup1408_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1408 group1408_128) :=
  @jointSecond fullProfiles freePoints restriction 1408 64 group1408_64 group1472_64 (by decide +kernel) covergroup1408_64 covergroup1472_64
private theorem covergroup1536_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1536 group1536_128) :=
  @jointSecond fullProfiles freePoints restriction 1536 64 group1536_64 group1600_64 (by decide +kernel) covergroup1536_64 covergroup1600_64
private theorem covergroup1664_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1664 group1664_128) :=
  @jointSecond fullProfiles freePoints restriction 1664 64 group1664_64 group1728_64 (by decide +kernel) covergroup1664_64 covergroup1728_64
private theorem covergroup1792_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1792 group1792_128) :=
  @jointSecond fullProfiles freePoints restriction 1792 64 group1792_64 group1856_64 (by decide +kernel) covergroup1792_64 covergroup1856_64
private theorem covergroup1920_128 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1920 group1920_128) :=
  @jointSecond fullProfiles freePoints restriction 1920 64 group1920_64 group1984_64 (by decide +kernel) covergroup1920_64 covergroup1984_64
private theorem covergroup0_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_256) :=
  @jointSecond fullProfiles freePoints restriction 0 128 group0_128 group128_128 (by decide +kernel) covergroup0_128 covergroup128_128
private theorem covergroup256_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 256 group256_256) :=
  @jointSecond fullProfiles freePoints restriction 256 128 group256_128 group384_128 (by decide +kernel) covergroup256_128 covergroup384_128
private theorem covergroup512_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 512 group512_256) :=
  @jointSecond fullProfiles freePoints restriction 512 128 group512_128 group640_128 (by decide +kernel) covergroup512_128 covergroup640_128
private theorem covergroup768_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 768 group768_256) :=
  @jointSecond fullProfiles freePoints restriction 768 128 group768_128 group896_128 (by decide +kernel) covergroup768_128 covergroup896_128
private theorem covergroup1024_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1024 group1024_256) :=
  @jointSecond fullProfiles freePoints restriction 1024 128 group1024_128 group1152_128 (by decide +kernel) covergroup1024_128 covergroup1152_128
private theorem covergroup1280_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1280 group1280_256) :=
  @jointSecond fullProfiles freePoints restriction 1280 128 group1280_128 group1408_128 (by decide +kernel) covergroup1280_128 covergroup1408_128
private theorem covergroup1536_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1536 group1536_256) :=
  @jointSecond fullProfiles freePoints restriction 1536 128 group1536_128 group1664_128 (by decide +kernel) covergroup1536_128 covergroup1664_128
private theorem covergroup1792_256 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1792 group1792_256) :=
  @jointSecond fullProfiles freePoints restriction 1792 128 group1792_128 group1920_128 (by decide +kernel) covergroup1792_128 covergroup1920_128
private theorem covergroup0_512 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_512) :=
  @jointSecond fullProfiles freePoints restriction 0 256 group0_256 group256_256 (by decide +kernel) covergroup0_256 covergroup256_256
private theorem covergroup512_512 : CertifiedList false fullProfiles (secondCodes freePoints restriction 512 group512_512) :=
  @jointSecond fullProfiles freePoints restriction 512 256 group512_256 group768_256 (by decide +kernel) covergroup512_256 covergroup768_256
private theorem covergroup1024_512 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1024 group1024_512) :=
  @jointSecond fullProfiles freePoints restriction 1024 256 group1024_256 group1280_256 (by decide +kernel) covergroup1024_256 covergroup1280_256
private theorem covergroup1536_512 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1536 group1536_512) :=
  @jointSecond fullProfiles freePoints restriction 1536 256 group1536_256 group1792_256 (by decide +kernel) covergroup1536_256 covergroup1792_256
private theorem covergroup0_1024 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_1024) :=
  @jointSecond fullProfiles freePoints restriction 0 512 group0_512 group512_512 (by decide +kernel) covergroup0_512 covergroup512_512
private theorem covergroup1024_1024 : CertifiedList false fullProfiles (secondCodes freePoints restriction 1024 group1024_1024) :=
  @jointSecond fullProfiles freePoints restriction 1024 512 group1024_512 group1536_512 (by decide +kernel) covergroup1024_512 covergroup1536_512
private theorem covergroup0_2048 : CertifiedList false fullProfiles (secondCodes freePoints restriction 0 group0_2048) :=
  @jointSecond fullProfiles freePoints restriction 0 1024 group0_1024 group1024_1024 (by decide +kernel) covergroup0_1024 covergroup1024_1024
theorem profile_case : ProfileCase restriction := by
  have names : freePoints=tailFree := by decide +kernel
  refine ⟨rows,rows_length,?_,?_⟩
  · intro c low
    have bound := (threshold_iff c).mp (by simpa only [names] using low)
    exact (coverage _ _ _ (field_lt ..) (field_lt ..) (field_lt ..)).mp (by simpa only [Nat.zero_add] using bound)
  · simpa only [names] using covergroup0_2048
end Quadric.Five.Census.Block.Case09
