import Quadric.Five.Moves

namespace Quadric.Five.Moves
open Small

def fuse : ℕ → List Line → List Line → List Line
  | 0,xs,ys => xs++ys
  | _+1,[],ys => ys
  | _+1,xs,[] => xs
  | n+1,x::xs,y::ys =>
    if code x ≤ code y then x::fuse n xs (y::ys) else y::fuse n (x::xs) ys

theorem fuse_perm (n : ℕ) (xs ys : List Line) : (fuse n xs ys).Perm (xs++ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [fuse]
    | cons x xs =>
      cases ys with
      | nil => simp [fuse]
      | cons y ys =>
        unfold fuse; split
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans (List.perm_middle ..).symm

def orderFuel : ℕ → List Line → List Line
  | 0,xs=>xs
  | n+1,xs=>
    if xs.length<2 then xs else
      let m:=xs.length/2
      fuse xs.length (orderFuel n (xs.take m)) (orderFuel n (xs.drop m))

theorem order_perm (n : ℕ) (xs : List Line) : (orderFuel n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    unfold orderFuel; split
    · exact List.Perm.refl _
    · exact (fuse_perm ..).trans (by simpa only [List.take_append_drop] using (ih (xs.take (xs.length/2))).append (ih (xs.drop (xs.length/2))))

def fastLineOK (m : Move) (ls : List Line) :=
  decide (orderFuel 11 (ls.map (relabel m))=orderFuel 11 ls)
theorem fastLine_perm {ls : List Line} {m : Move} (h : fastLineOK m ls=true) :
    (ls.map (relabel m)).Perm ls := by
  have left:=(order_perm 11 (ls.map (relabel m))).symm
  rw [of_decide_eq_true h] at left
  exact left.trans (order_perm 11 ls)

end Quadric.Five.Moves
