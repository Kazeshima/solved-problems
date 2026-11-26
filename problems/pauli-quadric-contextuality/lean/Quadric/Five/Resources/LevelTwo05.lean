import Quadric.Five.Resources.RChecked05
import Quadric.Five.Resources.Prepare05

namespace Quadric.Five.Census.Block.Case05
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
noncomputable def group0_64 := row0 ++ row32
private theorem checkedgroup0_64 : Segment system t0 t1 t2 0 64 group0_64 :=
  @Segment.join system t0 t1 t2 0 32 32 row0 row32 leaf0 leaf32
noncomputable def group64_64 := row64 ++ row96
private theorem checkedgroup64_64 : Segment system t0 t1 t2 64 64 group64_64 :=
  @Segment.join system t0 t1 t2 64 32 32 row64 row96 leaf64 leaf96
noncomputable def group128_64 := row128 ++ row160
private theorem checkedgroup128_64 : Segment system t0 t1 t2 128 64 group128_64 :=
  @Segment.join system t0 t1 t2 128 32 32 row128 row160 leaf128 leaf160
noncomputable def group192_64 := row192 ++ row224
private theorem checkedgroup192_64 : Segment system t0 t1 t2 192 64 group192_64 :=
  @Segment.join system t0 t1 t2 192 32 32 row192 row224 leaf192 leaf224
noncomputable def group256_64 := row256 ++ row288
private theorem checkedgroup256_64 : Segment system t0 t1 t2 256 64 group256_64 :=
  @Segment.join system t0 t1 t2 256 32 32 row256 row288 leaf256 leaf288
noncomputable def group320_64 := row320 ++ row352
private theorem checkedgroup320_64 : Segment system t0 t1 t2 320 64 group320_64 :=
  @Segment.join system t0 t1 t2 320 32 32 row320 row352 leaf320 leaf352
noncomputable def group384_64 := row384 ++ row416
private theorem checkedgroup384_64 : Segment system t0 t1 t2 384 64 group384_64 :=
  @Segment.join system t0 t1 t2 384 32 32 row384 row416 leaf384 leaf416
noncomputable def group448_64 := row448 ++ row480
private theorem checkedgroup448_64 : Segment system t0 t1 t2 448 64 group448_64 :=
  @Segment.join system t0 t1 t2 448 32 32 row448 row480 leaf448 leaf480
noncomputable def group512_64 := row512 ++ row544
private theorem checkedgroup512_64 : Segment system t0 t1 t2 512 64 group512_64 :=
  @Segment.join system t0 t1 t2 512 32 32 row512 row544 leaf512 leaf544
noncomputable def group576_64 := row576 ++ row608
private theorem checkedgroup576_64 : Segment system t0 t1 t2 576 64 group576_64 :=
  @Segment.join system t0 t1 t2 576 32 32 row576 row608 leaf576 leaf608
noncomputable def group640_64 := row640 ++ row672
private theorem checkedgroup640_64 : Segment system t0 t1 t2 640 64 group640_64 :=
  @Segment.join system t0 t1 t2 640 32 32 row640 row672 leaf640 leaf672
noncomputable def group704_64 := row704 ++ row736
private theorem checkedgroup704_64 : Segment system t0 t1 t2 704 64 group704_64 :=
  @Segment.join system t0 t1 t2 704 32 32 row704 row736 leaf704 leaf736
noncomputable def group768_64 := row768 ++ row800
private theorem checkedgroup768_64 : Segment system t0 t1 t2 768 64 group768_64 :=
  @Segment.join system t0 t1 t2 768 32 32 row768 row800 leaf768 leaf800
noncomputable def group832_64 := row832 ++ row864
private theorem checkedgroup832_64 : Segment system t0 t1 t2 832 64 group832_64 :=
  @Segment.join system t0 t1 t2 832 32 32 row832 row864 leaf832 leaf864
noncomputable def group896_64 := row896 ++ row928
private theorem checkedgroup896_64 : Segment system t0 t1 t2 896 64 group896_64 :=
  @Segment.join system t0 t1 t2 896 32 32 row896 row928 leaf896 leaf928
noncomputable def group960_64 := row960 ++ row992
private theorem checkedgroup960_64 : Segment system t0 t1 t2 960 64 group960_64 :=
  @Segment.join system t0 t1 t2 960 32 32 row960 row992 leaf960 leaf992
noncomputable def group1024_64 := row1024 ++ row1056
private theorem checkedgroup1024_64 : Segment system t0 t1 t2 1024 64 group1024_64 :=
  @Segment.join system t0 t1 t2 1024 32 32 row1024 row1056 leaf1024 leaf1056
noncomputable def group1088_64 := row1088 ++ row1120
private theorem checkedgroup1088_64 : Segment system t0 t1 t2 1088 64 group1088_64 :=
  @Segment.join system t0 t1 t2 1088 32 32 row1088 row1120 leaf1088 leaf1120
noncomputable def group1152_64 := row1152 ++ row1184
private theorem checkedgroup1152_64 : Segment system t0 t1 t2 1152 64 group1152_64 :=
  @Segment.join system t0 t1 t2 1152 32 32 row1152 row1184 leaf1152 leaf1184
noncomputable def group1216_64 := row1216 ++ row1248
private theorem checkedgroup1216_64 : Segment system t0 t1 t2 1216 64 group1216_64 :=
  @Segment.join system t0 t1 t2 1216 32 32 row1216 row1248 leaf1216 leaf1248
noncomputable def group1280_64 := row1280 ++ row1312
private theorem checkedgroup1280_64 : Segment system t0 t1 t2 1280 64 group1280_64 :=
  @Segment.join system t0 t1 t2 1280 32 32 row1280 row1312 leaf1280 leaf1312
noncomputable def group1344_64 := row1344 ++ row1376
private theorem checkedgroup1344_64 : Segment system t0 t1 t2 1344 64 group1344_64 :=
  @Segment.join system t0 t1 t2 1344 32 32 row1344 row1376 leaf1344 leaf1376
noncomputable def group1408_64 := row1408 ++ row1440
private theorem checkedgroup1408_64 : Segment system t0 t1 t2 1408 64 group1408_64 :=
  @Segment.join system t0 t1 t2 1408 32 32 row1408 row1440 leaf1408 leaf1440
noncomputable def group1472_64 := row1472 ++ row1504
private theorem checkedgroup1472_64 : Segment system t0 t1 t2 1472 64 group1472_64 :=
  @Segment.join system t0 t1 t2 1472 32 32 row1472 row1504 leaf1472 leaf1504
noncomputable def group1536_64 := row1536 ++ row1568
private theorem checkedgroup1536_64 : Segment system t0 t1 t2 1536 64 group1536_64 :=
  @Segment.join system t0 t1 t2 1536 32 32 row1536 row1568 leaf1536 leaf1568
noncomputable def group1600_64 := row1600 ++ row1632
private theorem checkedgroup1600_64 : Segment system t0 t1 t2 1600 64 group1600_64 :=
  @Segment.join system t0 t1 t2 1600 32 32 row1600 row1632 leaf1600 leaf1632
noncomputable def group1664_64 := row1664 ++ row1696
private theorem checkedgroup1664_64 : Segment system t0 t1 t2 1664 64 group1664_64 :=
  @Segment.join system t0 t1 t2 1664 32 32 row1664 row1696 leaf1664 leaf1696
noncomputable def group1728_64 := row1728 ++ row1760
private theorem checkedgroup1728_64 : Segment system t0 t1 t2 1728 64 group1728_64 :=
  @Segment.join system t0 t1 t2 1728 32 32 row1728 row1760 leaf1728 leaf1760
noncomputable def group1792_64 := row1792 ++ row1824
private theorem checkedgroup1792_64 : Segment system t0 t1 t2 1792 64 group1792_64 :=
  @Segment.join system t0 t1 t2 1792 32 32 row1792 row1824 leaf1792 leaf1824
noncomputable def group1856_64 := row1856 ++ row1888
private theorem checkedgroup1856_64 : Segment system t0 t1 t2 1856 64 group1856_64 :=
  @Segment.join system t0 t1 t2 1856 32 32 row1856 row1888 leaf1856 leaf1888
noncomputable def group1920_64 := row1920 ++ row1952
private theorem checkedgroup1920_64 : Segment system t0 t1 t2 1920 64 group1920_64 :=
  @Segment.join system t0 t1 t2 1920 32 32 row1920 row1952 leaf1920 leaf1952
noncomputable def group1984_64 := row1984 ++ row2016
private theorem checkedgroup1984_64 : Segment system t0 t1 t2 1984 64 group1984_64 :=
  @Segment.join system t0 t1 t2 1984 32 32 row1984 row2016 leaf1984 leaf2016
noncomputable def group0_128 := group0_64 ++ group64_64
private theorem checkedgroup0_128 : Segment system t0 t1 t2 0 128 group0_128 :=
  @Segment.join system t0 t1 t2 0 64 64 group0_64 group64_64 checkedgroup0_64 checkedgroup64_64
noncomputable def group128_128 := group128_64 ++ group192_64
private theorem checkedgroup128_128 : Segment system t0 t1 t2 128 128 group128_128 :=
  @Segment.join system t0 t1 t2 128 64 64 group128_64 group192_64 checkedgroup128_64 checkedgroup192_64
noncomputable def group256_128 := group256_64 ++ group320_64
private theorem checkedgroup256_128 : Segment system t0 t1 t2 256 128 group256_128 :=
  @Segment.join system t0 t1 t2 256 64 64 group256_64 group320_64 checkedgroup256_64 checkedgroup320_64
noncomputable def group384_128 := group384_64 ++ group448_64
private theorem checkedgroup384_128 : Segment system t0 t1 t2 384 128 group384_128 :=
  @Segment.join system t0 t1 t2 384 64 64 group384_64 group448_64 checkedgroup384_64 checkedgroup448_64
noncomputable def group512_128 := group512_64 ++ group576_64
private theorem checkedgroup512_128 : Segment system t0 t1 t2 512 128 group512_128 :=
  @Segment.join system t0 t1 t2 512 64 64 group512_64 group576_64 checkedgroup512_64 checkedgroup576_64
noncomputable def group640_128 := group640_64 ++ group704_64
private theorem checkedgroup640_128 : Segment system t0 t1 t2 640 128 group640_128 :=
  @Segment.join system t0 t1 t2 640 64 64 group640_64 group704_64 checkedgroup640_64 checkedgroup704_64
noncomputable def group768_128 := group768_64 ++ group832_64
private theorem checkedgroup768_128 : Segment system t0 t1 t2 768 128 group768_128 :=
  @Segment.join system t0 t1 t2 768 64 64 group768_64 group832_64 checkedgroup768_64 checkedgroup832_64
noncomputable def group896_128 := group896_64 ++ group960_64
private theorem checkedgroup896_128 : Segment system t0 t1 t2 896 128 group896_128 :=
  @Segment.join system t0 t1 t2 896 64 64 group896_64 group960_64 checkedgroup896_64 checkedgroup960_64
noncomputable def group1024_128 := group1024_64 ++ group1088_64
private theorem checkedgroup1024_128 : Segment system t0 t1 t2 1024 128 group1024_128 :=
  @Segment.join system t0 t1 t2 1024 64 64 group1024_64 group1088_64 checkedgroup1024_64 checkedgroup1088_64
noncomputable def group1152_128 := group1152_64 ++ group1216_64
private theorem checkedgroup1152_128 : Segment system t0 t1 t2 1152 128 group1152_128 :=
  @Segment.join system t0 t1 t2 1152 64 64 group1152_64 group1216_64 checkedgroup1152_64 checkedgroup1216_64
noncomputable def group1280_128 := group1280_64 ++ group1344_64
private theorem checkedgroup1280_128 : Segment system t0 t1 t2 1280 128 group1280_128 :=
  @Segment.join system t0 t1 t2 1280 64 64 group1280_64 group1344_64 checkedgroup1280_64 checkedgroup1344_64
noncomputable def group1408_128 := group1408_64 ++ group1472_64
private theorem checkedgroup1408_128 : Segment system t0 t1 t2 1408 128 group1408_128 :=
  @Segment.join system t0 t1 t2 1408 64 64 group1408_64 group1472_64 checkedgroup1408_64 checkedgroup1472_64
noncomputable def group1536_128 := group1536_64 ++ group1600_64
private theorem checkedgroup1536_128 : Segment system t0 t1 t2 1536 128 group1536_128 :=
  @Segment.join system t0 t1 t2 1536 64 64 group1536_64 group1600_64 checkedgroup1536_64 checkedgroup1600_64
noncomputable def group1664_128 := group1664_64 ++ group1728_64
private theorem checkedgroup1664_128 : Segment system t0 t1 t2 1664 128 group1664_128 :=
  @Segment.join system t0 t1 t2 1664 64 64 group1664_64 group1728_64 checkedgroup1664_64 checkedgroup1728_64
noncomputable def group1792_128 := group1792_64 ++ group1856_64
private theorem checkedgroup1792_128 : Segment system t0 t1 t2 1792 128 group1792_128 :=
  @Segment.join system t0 t1 t2 1792 64 64 group1792_64 group1856_64 checkedgroup1792_64 checkedgroup1856_64
noncomputable def group1920_128 := group1920_64 ++ group1984_64
private theorem checkedgroup1920_128 : Segment system t0 t1 t2 1920 128 group1920_128 :=
  @Segment.join system t0 t1 t2 1920 64 64 group1920_64 group1984_64 checkedgroup1920_64 checkedgroup1984_64
noncomputable def group0_256 := group0_128 ++ group128_128
private theorem checkedgroup0_256 : Segment system t0 t1 t2 0 256 group0_256 :=
  @Segment.join system t0 t1 t2 0 128 128 group0_128 group128_128 checkedgroup0_128 checkedgroup128_128
noncomputable def group256_256 := group256_128 ++ group384_128
private theorem checkedgroup256_256 : Segment system t0 t1 t2 256 256 group256_256 :=
  @Segment.join system t0 t1 t2 256 128 128 group256_128 group384_128 checkedgroup256_128 checkedgroup384_128
noncomputable def group512_256 := group512_128 ++ group640_128
private theorem checkedgroup512_256 : Segment system t0 t1 t2 512 256 group512_256 :=
  @Segment.join system t0 t1 t2 512 128 128 group512_128 group640_128 checkedgroup512_128 checkedgroup640_128
noncomputable def group768_256 := group768_128 ++ group896_128
private theorem checkedgroup768_256 : Segment system t0 t1 t2 768 256 group768_256 :=
  @Segment.join system t0 t1 t2 768 128 128 group768_128 group896_128 checkedgroup768_128 checkedgroup896_128
noncomputable def group1024_256 := group1024_128 ++ group1152_128
private theorem checkedgroup1024_256 : Segment system t0 t1 t2 1024 256 group1024_256 :=
  @Segment.join system t0 t1 t2 1024 128 128 group1024_128 group1152_128 checkedgroup1024_128 checkedgroup1152_128
noncomputable def group1280_256 := group1280_128 ++ group1408_128
private theorem checkedgroup1280_256 : Segment system t0 t1 t2 1280 256 group1280_256 :=
  @Segment.join system t0 t1 t2 1280 128 128 group1280_128 group1408_128 checkedgroup1280_128 checkedgroup1408_128
noncomputable def group1536_256 := group1536_128 ++ group1664_128
private theorem checkedgroup1536_256 : Segment system t0 t1 t2 1536 256 group1536_256 :=
  @Segment.join system t0 t1 t2 1536 128 128 group1536_128 group1664_128 checkedgroup1536_128 checkedgroup1664_128
noncomputable def group1792_256 := group1792_128 ++ group1920_128
private theorem checkedgroup1792_256 : Segment system t0 t1 t2 1792 256 group1792_256 :=
  @Segment.join system t0 t1 t2 1792 128 128 group1792_128 group1920_128 checkedgroup1792_128 checkedgroup1920_128
noncomputable def group0_512 := group0_256 ++ group256_256
private theorem checkedgroup0_512 : Segment system t0 t1 t2 0 512 group0_512 :=
  @Segment.join system t0 t1 t2 0 256 256 group0_256 group256_256 checkedgroup0_256 checkedgroup256_256
noncomputable def group512_512 := group512_256 ++ group768_256
private theorem checkedgroup512_512 : Segment system t0 t1 t2 512 512 group512_512 :=
  @Segment.join system t0 t1 t2 512 256 256 group512_256 group768_256 checkedgroup512_256 checkedgroup768_256
noncomputable def group1024_512 := group1024_256 ++ group1280_256
private theorem checkedgroup1024_512 : Segment system t0 t1 t2 1024 512 group1024_512 :=
  @Segment.join system t0 t1 t2 1024 256 256 group1024_256 group1280_256 checkedgroup1024_256 checkedgroup1280_256
noncomputable def group1536_512 := group1536_256 ++ group1792_256
private theorem checkedgroup1536_512 : Segment system t0 t1 t2 1536 512 group1536_512 :=
  @Segment.join system t0 t1 t2 1536 256 256 group1536_256 group1792_256 checkedgroup1536_256 checkedgroup1792_256
noncomputable def group0_1024 := group0_512 ++ group512_512
private theorem checkedgroup0_1024 : Segment system t0 t1 t2 0 1024 group0_1024 :=
  @Segment.join system t0 t1 t2 0 512 512 group0_512 group512_512 checkedgroup0_512 checkedgroup512_512
noncomputable def group1024_1024 := group1024_512 ++ group1536_512
private theorem checkedgroup1024_1024 : Segment system t0 t1 t2 1024 1024 group1024_1024 :=
  @Segment.join system t0 t1 t2 1024 512 512 group1024_512 group1536_512 checkedgroup1024_512 checkedgroup1536_512
noncomputable def group0_2048 := group0_1024 ++ group1024_1024
private theorem checkedgroup0_2048 : Segment system t0 t1 t2 0 2048 group0_2048 :=
  @Segment.join system t0 t1 t2 0 1024 1024 group0_1024 group1024_1024 checkedgroup0_1024 checkedgroup1024_1024
noncomputable def rows := group0_2048
theorem accepted : run system t0 t1 t2 0 rows=true := checkedgroup0_2048.2
theorem rows_length : rows.length=2048 := checkedgroup0_2048.1
theorem coverage (h a b : ℕ) (hh : h<2048) (ha : a<1024) (hb : b<1024) :
    fullCost system (0+h) a b ≤ system.cutoff ↔ member (rows[h]'(rows_length.symm ▸ hh)) a b := by
  have ok : run system (buildT system.first) (buildT system.second) (buildT system.crossBlock) 0 rows=true := by rw [table0,table1,table2]; exact accepted
  exact run_sound system prep 0 rows ok h a b (rows_length.symm ▸ hh) ha hb
end Quadric.Five.Census.Block.Case05
