import Quadric.Five.SmallGeometry

namespace Quadric.Five.Small
open Schur

def total {α : Type*} (xs : List α) (f : α→ℤ) := (xs.map f).sum

@[simp] theorem total_nil {α : Type*} (f : α→ℤ) : total [] f=0 := rfl
@[simp] theorem total_cons {α : Type*} (x : α) (xs : List α) (f : α→ℤ) :
    total (x::xs) f=f x+total xs f := rfl
theorem total_congr {α : Type*} (xs : List α) {f g : α→ℤ} (h : ∀ x∈xs, f x=g x) :
    total xs f=total xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [total_cons,total_cons,h a (by simp),ih (fun x hx => h x (by simp [hx]))]
theorem total_add {α : Type*} (xs : List α) (f g : α→ℤ) :
    total xs (fun x => f x+g x)=total xs f+total xs g := by
  induction xs with | nil => simp | cons a as ih => simp only [total_cons,ih]; ring
theorem total_sub {α : Type*} (xs : List α) (f g : α→ℤ) :
    total xs (fun x => f x-g x)=total xs f-total xs g := by
  induction xs with | nil => simp | cons a as ih => simp only [total_cons,ih]; ring
theorem total_mul {α : Type*} (xs : List α) (a : ℤ) (f : α→ℤ) :
    total xs (fun x => a*f x)=a*total xs f := by
  induction xs with | nil => simp | cons b bs ih => simp only [total_cons,ih]; ring
theorem total_zero {α : Type*} (xs : List α) : total xs (fun _ => 0)=0 := by
  induction xs <;> simp_all
theorem total_comm {α β : Type*} (xs : List α) (ys : List β) (f : α→β→ℤ) :
    total xs (fun x => total ys (f x))=total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total_zero]
  | cons a as ih => simp only [total_cons,ih,total_add]
theorem total_le {α : Type*} (xs : List α) {f g : α→ℤ} (h : ∀ x∈xs,f x≤g x) :
    total xs f ≤ total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact add_le_add (h _ (by simp)) (ih fun y hy => h y (by simp [hy]))
theorem total_map {α β : Type*} (xs : List α) (f : α→β) (g : β→ℤ) :
    total (xs.map f) g=total xs (fun x => g (f x)) := by simp [total,List.map_map,Function.comp_def]
theorem total_append {α : Type*} (xs ys : List α) (f : α→ℤ) :
    total (xs++ys) f=total xs f+total ys f := by
  induction xs with
  | nil => simp
  | cons a as ih => simp only [List.cons_append,total_cons,ih]; ring
theorem total_mark {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (xs : List α) (a : α) (f : α→ℤ) :
    total xs (fun x => if x=a then f x else 0)=xs.count a*f a := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    by_cases he : b=a <;> simp [he,ih,List.count_cons] <;> ring

def upper {α : Type*} (diag : α→ℤ) (off : α→α→ℤ) : List α → List (List ℤ)
  | [] => []
  | a::as => (diag a::as.map (off a)) :: upper diag off as

theorem dot_map {α : Type*} (xs : List α) (f g : α→ℤ) :
    Schur.dot (xs.map f) (xs.map g)=total xs (fun x => f x*g x) := by
  induction xs <;> simp_all [Schur.dot]

theorem quad_upper {α : Type*} (xs : List α) (d : α→ℤ) (g : α→α→ℤ) (u : α→ℤ) :
    Schur.quad (upper d g xs) (xs.map u)=total xs (fun x => d x*(u x)^2) +
      2*total (pairs xs) (fun ij => g ij.1 ij.2*u ij.1*u ij.2) := by
  induction xs with
  | nil => simp [Schur.quad,upper,pairs]
  | cons a as ih =>
    simp only [upper,List.map_cons,Schur.quad,ih,dot_map,pairs,total_append,total_map,total_cons]
    have h : total as (fun x => g a x*u a*u x)=u a*total as (fun x => g a x*u x) := by
      rw [←total_mul]; exact total_congr _ fun _ _ => by ring
    rw [h]; ring

end Quadric.Five.Small
