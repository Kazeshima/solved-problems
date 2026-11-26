import Quadric.Five.Deposit
import Quadric.Five.OneBlock

namespace Quadric.Five.Census
open Block

def firstCodes (free : List ℕ) : ℕ→List (List ℕ)→List ℕ
  | _,[]=>[]
  | h,row::rs=>(row.map fun l=>deposit free (65536*h+l)) ++ firstCodes free (h+1) rs

theorem first_mem (free : List ℕ) (h : ℕ) (rows : List (List ℕ)) (j l : ℕ)
    (hj : j<rows.length) (hl : l∈rows[j]) :
    deposit free (65536*(h+j)+l)∈firstCodes free h rows := by
  induction rows generalizing h j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero => apply List.mem_append_left; exact List.mem_map.mpr ⟨l,hl,by simp⟩
    | succ j =>
      apply List.mem_append_right
      simpa only [show h+(j+1)=(h+1)+j by omega] using ih (h+1) j (by simpa using hj) hl

def codeRow (free : List ℕ) (rep h : ℕ) (r : Block.Row) := r.slices.flatMap (fun v=>
  v.2.map fun b=>rep ||| deposit free (1048576*h+1024*b+v.1))

def secondCodes (free : List ℕ) (rep : ℕ) : ℕ→List Block.Row→List ℕ
  | _,[]=>[]
  | h,r::rs=>codeRow free rep h r ++ secondCodes free rep (h+1) rs

theorem code_row_mem (free : List ℕ) (rep h : ℕ) (r : Block.Row) (a b : ℕ) (hw : member r a b) :
    (rep ||| deposit free (1048576*h+1024*b+a)) ∈ codeRow free rep h r := by
  obtain ⟨v,hv,he,hb⟩:=hw
  apply List.mem_flatMap.mpr; exact ⟨v,hv,List.mem_map.mpr ⟨b,hb,by rw [he]⟩⟩

theorem second_mem (free : List ℕ) (rep h : ℕ) (rows : List Block.Row) (j a b : ℕ) (hj : j<rows.length)
    (hw : member rows[j] a b) :
    (rep ||| deposit free (1048576*(h+j)+1024*b+a))∈secondCodes free rep h rows := by
  induction rows generalizing h j with
  | nil => simp at hj
  | cons r rs ih =>
    cases j with
    | zero => apply List.mem_append_left; simpa using code_row_mem free rep h r a b hw
    | succ j =>
      apply List.mem_append_right
      simpa only [show h+(j+1)=(h+1)+j by omega] using ih (h+1) j (by simpa using hj) hw

end Quadric.Five.Census

