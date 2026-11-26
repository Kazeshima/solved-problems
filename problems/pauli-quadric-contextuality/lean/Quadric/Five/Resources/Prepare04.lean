import Quadric.Five.Intervals
import Quadric.Five.Resources.System04

namespace Quadric.Five.Census.Block.Case04
set_option maxRecDepth 16384
set_option maxHeartbeats 24000000
set_option Elab.async false
private theorem cross0 : Interval (crossCheck system t2) 0 32 :=
  interval_checked (by decide +kernel)
private theorem cross32 : Interval (crossCheck system t2) 32 32 :=
  interval_checked (by decide +kernel)
private theorem cross64 : Interval (crossCheck system t2) 64 32 :=
  interval_checked (by decide +kernel)
private theorem cross96 : Interval (crossCheck system t2) 96 32 :=
  interval_checked (by decide +kernel)
private theorem cross128 : Interval (crossCheck system t2) 128 32 :=
  interval_checked (by decide +kernel)
private theorem cross160 : Interval (crossCheck system t2) 160 32 :=
  interval_checked (by decide +kernel)
private theorem cross192 : Interval (crossCheck system t2) 192 32 :=
  interval_checked (by decide +kernel)
private theorem cross224 : Interval (crossCheck system t2) 224 32 :=
  interval_checked (by decide +kernel)
private theorem cross256 : Interval (crossCheck system t2) 256 32 :=
  interval_checked (by decide +kernel)
private theorem cross288 : Interval (crossCheck system t2) 288 32 :=
  interval_checked (by decide +kernel)
private theorem cross320 : Interval (crossCheck system t2) 320 32 :=
  interval_checked (by decide +kernel)
private theorem cross352 : Interval (crossCheck system t2) 352 32 :=
  interval_checked (by decide +kernel)
private theorem cross384 : Interval (crossCheck system t2) 384 32 :=
  interval_checked (by decide +kernel)
private theorem cross416 : Interval (crossCheck system t2) 416 32 :=
  interval_checked (by decide +kernel)
private theorem cross448 : Interval (crossCheck system t2) 448 32 :=
  interval_checked (by decide +kernel)
private theorem cross480 : Interval (crossCheck system t2) 480 32 :=
  interval_checked (by decide +kernel)
private theorem cross512 : Interval (crossCheck system t2) 512 32 :=
  interval_checked (by decide +kernel)
private theorem cross544 : Interval (crossCheck system t2) 544 32 :=
  interval_checked (by decide +kernel)
private theorem cross576 : Interval (crossCheck system t2) 576 32 :=
  interval_checked (by decide +kernel)
private theorem cross608 : Interval (crossCheck system t2) 608 32 :=
  interval_checked (by decide +kernel)
private theorem cross640 : Interval (crossCheck system t2) 640 32 :=
  interval_checked (by decide +kernel)
private theorem cross672 : Interval (crossCheck system t2) 672 32 :=
  interval_checked (by decide +kernel)
private theorem cross704 : Interval (crossCheck system t2) 704 32 :=
  interval_checked (by decide +kernel)
private theorem cross736 : Interval (crossCheck system t2) 736 32 :=
  interval_checked (by decide +kernel)
private theorem cross768 : Interval (crossCheck system t2) 768 32 :=
  interval_checked (by decide +kernel)
private theorem cross800 : Interval (crossCheck system t2) 800 32 :=
  interval_checked (by decide +kernel)
private theorem cross832 : Interval (crossCheck system t2) 832 32 :=
  interval_checked (by decide +kernel)
private theorem cross864 : Interval (crossCheck system t2) 864 32 :=
  interval_checked (by decide +kernel)
private theorem cross896 : Interval (crossCheck system t2) 896 32 :=
  interval_checked (by decide +kernel)
private theorem cross928 : Interval (crossCheck system t2) 928 32 :=
  interval_checked (by decide +kernel)
private theorem cross960 : Interval (crossCheck system t2) 960 32 :=
  interval_checked (by decide +kernel)
private theorem cross992 : Interval (crossCheck system t2) 992 32 :=
  interval_checked (by decide +kernel)
theorem prep : prepared system (buildT system.crossBlock)=true := by
  rw [table2]; apply prepare_parts system t2 (by decide +kernel)
  exact Interval.join cross0 (Interval.join cross32 (Interval.join cross64 (Interval.join cross96 (Interval.join cross128 (Interval.join cross160 (Interval.join cross192 (Interval.join cross224 (Interval.join cross256 (Interval.join cross288 (Interval.join cross320 (Interval.join cross352 (Interval.join cross384 (Interval.join cross416 (Interval.join cross448 (Interval.join cross480 (Interval.join cross512 (Interval.join cross544 (Interval.join cross576 (Interval.join cross608 (Interval.join cross640 (Interval.join cross672 (Interval.join cross704 (Interval.join cross736 (Interval.join cross768 (Interval.join cross800 (Interval.join cross832 (Interval.join cross864 (Interval.join cross896 (Interval.join cross928 (Interval.join cross960 (cross992)))))))))))))))))))))))))))))))
end Quadric.Five.Census.Block.Case04
