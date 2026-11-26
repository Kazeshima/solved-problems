import Quadric.Five.Certificates
import Quadric.Five.BasePoints
import Quadric.Incidence

namespace Quadric.Five.Tagged
open Small
open Finset
open scoped BigOperators

def lift3 (w : ℕ) := ys 3 w%2 + 2*xpart 3 w + 32*zpart 3 w
def outsideCoordinates : List ℕ :=
  [50,51,54,55,58,59,62,63,84,85,86,87,92,93,94,95,114,115,116,117,122,123,124,125,
   152,153,154,155,156,157,158,159,178,179,182,183,184,185,188,189,212,213,214,215,
   216,217,218,219,242,243,244,245,248,249,254,255]
theorem outside_coordinates : outsideCoordinates = outside := by decide +kernel
def physical (i : ℕ) := if i<64 then lift3 i else outsideCoordinates[i-64]?.getD 0
def point (i : ℕ) : Label 4 := Dual.decode (physical i)
def rephase (p : ℕ) := (ys 4 p / 2)%2 == 1
def bit (b : Bool) : Bit := if b then 1 else 0
theorem bit_xor (b c : Bool) : bit (b ^^ c)=bit b+bit c := by cases b <;> cases c <;> decide
theorem bit_nonzero (x : Bit) : bit (decide (x≠0))=x := by fin_cases x <;> decide

def signing (s : Signing 4) (i : ℕ) : Bool := decide (s (point i) ≠ 0) ^^ rephase (physical i)
def outsideLine (e : ℕ×ℕ) : Line :=
  let u:=outside[e.1]?.getD 0
  let v:=outside[e.2]?.getD 0
  ⟨drop (u^^^v),64+e.1,64+e.2,negative 4 u v⟩

def outsideLines := (edges.filter fun e=>isEdge e.1 e.2).map outsideLine
def ellipticLines := full3++outsideLines

def packFlags (keys : List ℕ) (f : ℕ→Bool) : ℕ :=
  keys.foldr (fun i v=>if f i then (2^i)|||v else v) 0
theorem flag_bit (keys : List ℕ) (f : ℕ→Bool) (i : ℕ) :
    (packFlags keys f).testBit i = (decide (i∈keys) && f i) := by
  induction keys with
  | nil => simp [packFlags]
  | cons a as ih =>
    by_cases he : i=a
    · subst i; cases h : f a <;> simp_all [packFlags,Nat.testBit_or,Nat.testBit_two_pow]
    · cases h : f a <;> simp_all [packFlags,Nat.testBit_or,Nat.testBit_two_pow,Ne.symm he]
def carrier (f : ℕ→Bool) := packFlags (List.range 64) f

theorem carrier_at (s : ℕ→Bool) (i : ℕ) (hi : i<64) : (carrier s).testBit i=s i := by
  simp [carrier,flag_bit,hi]

private theorem all_small : full3.all (fun l=>l.a<64 && l.b<64 && l.c<64)=true := by decide +kernel

theorem inner_count (s : ℕ→Bool) : errors full3 (carrier s).testBit = errors full3 s := by
  unfold errors; apply List.countP_congr
  intro l hl
  have hh := List.all_eq_true.mp all_small l hl
  simp only [Bool.and_eq_true_iff,decide_eq_true_eq] at hh
  simp [Small.failure,carrier_at s l.a hh.1.1,carrier_at s l.b hh.1.2,carrier_at s l.c hh.2]

private theorem small_drop : edges.all (fun e => drop ((outside[e.1]?.getD 0)^^^(outside[e.2]?.getD 0))<64) = true := by decide +kernel

theorem outside_count_eq (s : ℕ→Bool) : errors outsideLines s=
    Certificates.outsideErrors (carrier s) (fun i=>s (64+i)) := by
  unfold errors outsideLines Certificates.outsideErrors
  rw [List.countP_map,List.countP_filter]
  apply List.countP_congr
  rintro ⟨i,j⟩ he
  have hb := of_decide_eq_true (List.all_eq_true.mp small_drop (i,j) he)
  simp only [Function.comp_def,outsideLine,Small.failure,Certificates.edgeSpin,graph_eq,carrier_at s _ hb]
  generalize isEdge i j=a
  generalize negative 4 (outside[i]?.getD 0) (outside[j]?.getD 0)=v
  generalize s (drop ((outside[i]?.getD 0) ^^^ (outside[j]?.getD 0)))=u
  generalize s (64+i)=b
  generalize s (64+j)=c
  cases a <;> cases v <;> cases u <;> cases b <;> cases c <;> decide

theorem partition_errors (s : ℕ→Bool) : errors ellipticLines s=
    errors full3 (carrier s).testBit + Certificates.outsideErrors (carrier s) (fun i=>s (64+i)) := by
  change List.countP _ (full3++outsideLines)=_
  rw [List.countP_append]
  exact congrArg₂ (·+·) (inner_count s).symm (outside_count_eq s)

def six (l : Line) : List Line :=
  [l,⟨l.b,l.a,l.c,l.neg⟩,⟨l.a,l.c,l.b,l.neg⟩,⟨l.c,l.a,l.b,l.neg⟩,
    ⟨l.b,l.c,l.a,l.neg⟩,⟨l.c,l.b,l.a,l.neg⟩]

theorem failure_six (s : ℕ→Bool) (ls : List Line) :
    (ls.flatMap six).countP (failure s)=6*errors ls s := by
  have h (l : Line) : (six l).countP (failure s) = if failure s l then 6 else 0 := by
    rcases l with ⟨a,b,c,z⟩
    simp only [six,Small.failure,List.countP_cons,List.countP_nil]
    simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
    split <;> decide
  induction ls with
  | nil => simp [errors]
  | cons l ls ih =>
    simp only [List.flatMap_cons,List.countP_append,h,ih,errors,List.countP_cons]
    cases failure s l <;> simp <;> omega

/-- Boolean membership certificate for a genuine signed Pauli pair. -/
def lineCheck (inner : Bool) (l : Line) : Bool :=
  let p:=point l.a
  let r:=point l.b
  let t:=point l.c
  decide (p≠0 ∧ r≠0 ∧ t≠0 ∧ form ellipticBase p=0 ∧ form ellipticBase r=0 ∧
    form ellipticBase t=0 ∧ polar p r=0 ∧ p+r=t ∧
    bit (rephase (physical l.a))+bit (rephase (physical l.b))+bit (rephase (physical l.c))+
      bit l.neg=herm p r ∧
    (inner=true → polar p sectionBase=0 ∧ polar r sectionBase=0 ∧ polar t sectionBase=0))

def key (l : Line) := Dual.encode (point l.a)+256*Dual.encode (point l.b)

def fresh : ℕ → List ℕ → Bool
  | _,[]=>true
  | seen,k::ks=> !seen.testBit k && fresh (seen ||| (2^k)) ks

theorem fresh_sound (seen : ℕ) (ks : List ℕ) (h : fresh seen ks=true) :
    ks.Nodup ∧ ∀k∈ks,seen.testBit k=false := by
  induction ks generalizing seen with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha,hs⟩ := Bool.and_eq_true_iff.mp h
    have ha' : seen.testBit a=false := by simpa using ha
    obtain ⟨nd,hb⟩ := ih _ hs
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_,nd⟩; intro hh
      have := hb a hh; simp [Nat.testBit_or,Nat.testBit_two_pow] at this
    · intro k hk; rcases List.mem_cons.mp hk with rfl|hk
      · exact ha'
      · have := hb k hk; simpa [Nat.testBit_or] using (Bool.or_eq_false_iff.mp (by simpa only [Nat.testBit_or] using this)).1

def actualDomain (inner : Bool) :=
  if inner then slice (quadric ellipticBase) ellipticBase sectionBase else quadric ellipticBase

theorem line_sound (inner : Bool) (s : Signing 4) (l : Line) (h : lineCheck inner l=true)
    (bad : failure (signing s) l=true) :
    (point l.a,point l.b) ∈ faults (actualDomain inner) s := by
  obtain ⟨hp,hr,ht,hp0,hr0,ht0,hpr,hsum,he,hi⟩ := of_decide_eq_true h
  have mem (x : Label 4) (hn : x≠0) (hq : form ellipticBase x=0)
      (hf : inner=true → polar x sectionBase=0) : x∈actualDomain inner := by
    have hx : x∈quadric ellipticBase := mem_filter.mpr ⟨mem_erase.mpr ⟨hn,mem_univ _⟩,hq⟩
    cases ii : inner
    · simpa [actualDomain,ii] using hx
    · apply mem_filter.mpr; exact ⟨hx,(hf ii).trans hq.symm⟩
  apply mem_faults.mpr
  refine ⟨mem_contexts.mpr ⟨mem _ hp hp0 (fun h=>(hi h).1),mem _ hr hr0 (fun h=>(hi h).2.1),
    hsum ▸ mem _ ht ht0 (fun h=>(hi h).2.2),hpr⟩,?_⟩
  have hb := congrArg bit bad
  simp only [Small.failure,signing,bit_xor,bit_nonzero] at hb
  have eq : bitScore s (point l.a) (point l.b)=1 := by
    unfold bitScore; rw [hsum,←he]
    change _ = (bit true)
    convert hb using 1; abel
  rw [eq]; decide

theorem catalogue_lower (inner : Bool) (ls : List Line) (s : Signing 4)
    (hl : (ls.flatMap six).all (lineCheck inner)=true)
    (hn : fresh 0 ((ls.flatMap six).map key)=true) :
    6*errors ls (signing s) ≤ (faults (actualDomain inner) s).card := by
  classical
  let dirs := ls.flatMap six
  let fail := dirs.filter (failure (signing s))
  let pair (l : Line) := (point l.a,point l.b)
  have nd : (dirs.map key).Nodup := (fresh_sound _ _ hn).1
  have nd2 : (dirs.map pair).Nodup := by
    apply List.Nodup.of_map (fun z : Label 4 × Label 4 => Dual.encode z.1+256*Dual.encode z.2)
    simpa [List.map_map,Function.comp_def,key,pair] using nd
  have nd3 : (fail.map pair).Nodup := by
    apply List.Sublist.nodup _ nd2
    exact (List.filter_sublist (p:=failure (signing s)) (l:=dirs)).map pair
  have subset : (fail.map pair).toFinset ⊆ faults (actualDomain inner) s := by
    intro z hz
    obtain ⟨l,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    obtain ⟨hL,hbad⟩ := List.mem_filter.mp hm
    exact line_sound _ _ _ (List.all_eq_true.mp hl _ hL) hbad
  have bound := card_le_card subset
  rw [List.toFinset_card_of_nodup nd3,List.length_map] at bound
  change (dirs.filter (failure (signing s))).length ≤ _ at bound
  simpa only [←List.countP_eq_length_filter,dirs,failure_six] using bound

end Quadric.Five.Tagged
