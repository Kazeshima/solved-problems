import ZonotopeFlips

/-!
Concrete checks of the definition of consistency, by kernel evaluation (`decide`).
They are independent of the counting theorems.
-/

open ZonoFlips

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

/-- The path `0 - 1 - 2 - 3` is consistent. -/
example : Consistent (Finset.range 4) {(0, 1), (1, 2), (2, 3)} := by
  unfold Consistent MonoP DownP UpP adj
  decide

/-- The single edge `0 - 2` on four vertices is not: `{2}` is neither an initial nor a final
segment of `{1, 2, 3}`. -/
example : ¬ Consistent (Finset.range 4) {(0, 2)} := by
  unfold Consistent MonoP DownP UpP adj
  decide

/-- On three vertices every graph is consistent (so the flip graph is the 3-cube). -/
example : ∀ G ∈ graphs (Finset.range 3), Consistent (Finset.range 3) G := by
  unfold Consistent MonoP DownP UpP adj graphs pairs
  decide

/-- Adding the edge `0 - 3` to the path `0 - 1 - 2 - 3` breaks consistency, adding `0 - 2`
does not: the second is a flip, the first is not. -/
example : ¬ Consistent (Finset.range 4) (insert (0, 3) {(0, 1), (1, 2), (2, 3)}) := by
  unfold Consistent MonoP DownP UpP adj
  decide

example : Consistent (Finset.range 4) (insert (0, 2) {(0, 1), (1, 2), (2, 3)}) := by
  unfold Consistent MonoP DownP UpP adj
  decide
