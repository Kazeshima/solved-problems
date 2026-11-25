import Std

/-! Mutable-array reference and bitmask experiment. The proved operational semantics and Bellman bridge live in Operational.lean and Charging.lean. -/
namespace ShellMinimax.Exec

def gapPass (input : Array Nat) (h : Nat) : Array Nat × Nat := Id.run do
  if h == 0 then return (input, 0)
  let mut a := input
  let mut c := 0
  for i in [h:a.size] do
    let x := a[i]!
    let mut j := i
    for _ in [:i/h] do
      if j < h then break
      c := c + 1
      if a[j-h]! < x then break
      a := a.set! j a[j-h]!
      j := j-h
    a := a.set! j x
  return (a, c)

def shell (a : Array Nat) (gaps : List Nat) : Array Nat × Nat :=
  gaps.foldl (fun ac h =>
    let bc := gapPass ac.1 h
    (bc.1, ac.2 + bc.2)) (a, 0)

def chosen (mask i : Nat) : Bool := mask.testBit i

def binaryPass (n h mask : Nat) : Nat := Id.run do
  if h == 0 then return mask
  let mut t := 0
  for r in [:h] do
    let mut k := 0
    for i in [:n] do
      if i % h == r && chosen mask i then k := k+1
    for j in [:k] do
      t := t + 2^(r+j*h)
  return t

def edge (n : Nat) (gaps : List Nat) (mask x : Nat) : Nat := Id.run do
  let mut s := mask
  let mut pos := x
  let mut c := 0
  for h in gaps do
    if h > 0 then
      let mut small := 0
      let mut total := 0
      for i in [:n] do
        if i % h == pos % h && chosen s i then
          total := total + 1
          if i < pos then small := small+1
      c := c + (pos/h-small) + (if small > 0 then 1 else 0)
      s := binaryPass n h s
      pos := pos%h + h*total
  return c

def exactDP (n : Nat) (gaps : List Nat) : Nat := Id.run do
  let count := 2^n
  let mut dp := Array.replicate count (0 : Nat)
  for s in [:count] do
    for x in [:n] do
      if !(chosen s x) then
        let t := s + 2^x
        dp := dp.set! t (max dp[t]! (dp[s]! + edge n gaps s x))
  return dp[count-1]!

/-- The concrete witness gives a strict lower bound on a nonoptimal schedule. -/
def checkWitness (n : Nat) (gaps : List Nat) (upper : Nat) (p : List Nat) : Bool :=
  p.length == n && ((List.range n).all fun x => p.contains x) &&
    decide ((shell p.toArray gaps).2 > upper)

-- Executable smoke checks. Formal results are exported separately.
#eval exactDP 5 [3, 2, 1] -- expected 11
#eval exactDP 8 [7, 5, 1] -- expected 23

end ShellMinimax.Exec
