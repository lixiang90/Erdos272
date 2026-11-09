module

public import Erdos272.Resources.CleanupNet208
public import Erdos272.Arithmetic.LightPrice208
public import Erdos272.Arithmetic.WindowSums208
public import Erdos272.Arithmetic.CombinedCounts208
public import Erdos272.Arithmetic.StepClass208

@[expose] public section

namespace JSP233.CleanupEval208
open LightClosed208 CleanupNet208 WindowCounts208 WindowSums208 CombinedCounts208
open scoped BigOperators
set_option maxHeartbeats 0

structure Band where
  T : ℕ
  E : ℕ
  U : ℕ
  b2 : ℕ
  b3 : ℕ
  b5 : ℕ
  b7 : ℕ
  b11 : ℕ
  deriving DecidableEq,Repr
structure Row where
  grid : ℕ
  low : ℕ
  high : ℕ
  i : ℕ
  bands : List Band
  deriving DecidableEq,Repr
structure Totals where
  first : ℕ
  second : ℕ
  credit : ℕ
  net : ℕ
  light : ℕ
  deriving DecidableEq,Repr
def zero : Totals := ⟨0,0,0,0,0⟩
def add (a b : Totals) : Totals :=
  ⟨a.first+b.first,a.second+b.second,a.credit+b.credit,a.net+b.net,a.light+b.light⟩
structure BandValue where
  count : ℕ
  windows : ℕ
  credit : ℕ
  light : ℕ
  deriving DecidableEq,Repr
def bandZero : BandValue := ⟨0,0,0,0⟩
def bandAdd (a b : BandValue) : BandValue :=
  ⟨a.count+b.count,a.windows+b.windows,a.credit+b.credit,a.light+b.light⟩
def block (b : Band) (d : ℕ) : ℕ :=
  match StepClass208.PrimeGate d with
  | 2 => b.b2 | 3 => b.b3 | 5 => b.b5 | 7 => b.b7 | _ => b.b11

def bandValue (r : Row) (d : ℕ) (b : Band) : BandValue :=
  if b.E ≤ 1 then bandZero else
  let B:=block b d
  let V:=b.U+B-3
  let A:=b.T-b.E
  let K:=V-b.E
  let J:=K-1
  let ql:=r.low/d
  let qh:=r.high/d
  let h:=(V-1)/B+1
  let ordinary:=min h (Count qh K B)
  let C:=V+(ordinary-1)*B
  let recip:=Ceil r.grid d+Ceil r.grid r.low
  let one:=if 0<ordinary then min (Ceil (min C r.low*r.grid) r.low) recip else 0
  let nt:=maximum A J B ql qh
  let total:=maximum_sum A J B ql qh
  let two:=min (Ceil (min total r.low*r.grid) r.low) (nt*recip)
  let count:=maximum_combined A K B h ql qh
  ⟨count,one+two,count*(b.T*r.grid/r.high),LightPrice208.Closed r.high d b.T b.E B V⟩

def BandGood (r : Row) (d : ℕ) (b : Band) (v : BandValue) : Prop :=
  let B:=block b d
  let V:=b.U+B-3
  let p:=StepClass208.PrimeGate d
  1 ≤ b.E ∧ b.E ≤ r.i ∧ b.E ≤ b.T ∧ b.T<b.U ∧ 2 ≤ B ∧ B ≤ b.T-b.E ∧ b.T<V ∧
    ((p-1)*(b.T-b.E+1-B) ≥ b.E ∨ p*B ≤ (p-1)*(b.T-b.E+1)) ∧
    (0<v.count → (b.T-b.E+1)*r.grid ≤ min r.grid v.windows*r.high)
instance (r : Row) (d : ℕ) (b : Band) (v : BandValue) : Decidable (BandGood r d b v) := by
  unfold BandGood;infer_instance

structure BandFold where
  value : BandValue
  good : Bool
def foldBands (r : Row) (d : ℕ) : List Band → BandFold
  | [] => ⟨bandZero,true⟩
  | b::bs =>
    let v:=bandValue r d b
    let tail:=foldBands r d bs
    ⟨bandAdd v tail.value,decide (BandGood r d b v) && tail.good⟩

structure Chunk where
  totals : Totals
  good : Bool
def step (r : Row) (d : ℕ) : Chunk :=
  let b:=foldBands r d r.bands
  let Z:=min r.grid b.value.windows
  let first:=b.value.count*Z
  let second:=b.value.count*Ceil (r.i*r.grid) r.low
  ⟨⟨first,second,b.value.credit,first+second-b.value.credit,b.value.light⟩,
    b.good && decide (0<r.grid ∧ 0<r.low ∧ r.low ≤ r.high ∧ 0<d ∧ b.value.credit ≤ first+second)⟩

def run (r : Row) (start : ℕ) : ℕ → Chunk
  | 0 => ⟨zero,true⟩
  | n+1 =>
    let before:=run r start n
    let v:=step r (start+n)
    ⟨add before.totals v.totals,before.good && v.good⟩
def checkChunk (r : Row) (start len : ℕ) (expected : Totals) : Bool :=
  let result:=run r start len
  result.good && decide (result.totals=expected)

theorem run_good (r : Row) (start len : ℕ) (h : (run r start len).good=true) :
    ∀ k<len,(step r (start+k)).good=true := by
  induction len with
  | zero => intro k hk;omega
  | succ n ih =>
    have hh : (run r start n).good=true ∧ (step r (start+n)).good=true := by
      simpa only [run,Bool.and_eq_true] using h
    intro k hk
    by_cases he : k=n
    · simpa only [he] using hh.2
    · exact ih hh.1 k (by omega)

theorem run_summary (field : Totals → ℕ) (hz : field zero=0)
    (ha : ∀ a b,field (add a b)=field a+field b) (r : Row) (start len : ℕ) :
    field (run r start len).totals=∑ k∈Finset.range len,field (step r (start+k)).totals := by
  induction len with
  | zero => simpa only [run,Finset.sum_range_zero] using hz
  | succ n ih =>
    simpa only [run,ha,Finset.sum_range_succ] using congrArg
      (fun x=>x+field (step r (start+n)).totals) ih

structure ChunkFacts (r : Row) (start len : ℕ) (expected : Totals) : Prop where
  good : ∀ k<len,(step r (start+k)).good=true
  first_eq : expected.first=∑ k∈Finset.range len,(step r (start+k)).totals.first
  second_eq : expected.second=∑ k∈Finset.range len,(step r (start+k)).totals.second
  credit_eq : expected.credit=∑ k∈Finset.range len,(step r (start+k)).totals.credit
  net_eq : expected.net=∑ k∈Finset.range len,(step r (start+k)).totals.net
  light_eq : expected.light=∑ k∈Finset.range len,(step r (start+k)).totals.light

theorem check_sound {r : Row} {start len : ℕ} {expected : Totals}
    (h : checkChunk r start len expected=true) : ChunkFacts r start len expected := by
  have hh : (run r start len).good=true ∧ decide ((run r start len).totals=expected)=true := by
    simpa only [checkChunk,Bool.and_eq_true] using h
  have he : (run r start len).totals=expected := of_decide_eq_true hh.2
  refine ⟨run_good r start len hh.1,?_,?_,?_,?_,?_⟩
  · rw [←he];exact run_summary Totals.first rfl (fun a b=>rfl) r start len
  · rw [←he];exact run_summary Totals.second rfl (fun a b=>rfl) r start len
  · rw [←he];exact run_summary Totals.credit rfl (fun a b=>rfl) r start len
  · rw [←he];exact run_summary Totals.net rfl (fun a b=>rfl) r start len
  · rw [←he];exact run_summary Totals.light rfl (fun a b=>rfl) r start len

theorem fold_good {r : Row} {d : ℕ} {bs : List Band}
    (h : (foldBands r d bs).good=true) : ∀ b∈bs,BandGood r d b (bandValue r d b) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hh : decide (BandGood r d b (bandValue r d b))=true ∧ (foldBands r d bs).good=true := by
      simpa only [foldBands,Bool.and_eq_true] using h
    intro a ha
    rcases List.mem_cons.mp ha with he | ht
    · subst a;exact of_decide_eq_true hh.1
    · exact ih hh.2 a ht

theorem step_good {r : Row} {d : ℕ} (h : (step r d).good=true) :
    (∀ b∈r.bands,BandGood r d b (bandValue r d b)) ∧
      0<r.grid ∧ 0<r.low ∧ r.low ≤ r.high ∧ 0<d := by
  have hh : (foldBands r d r.bands).good=true ∧
      decide (0<r.grid ∧ 0<r.low ∧ r.low ≤ r.high ∧ 0<d ∧
        (foldBands r d r.bands).value.credit ≤ 
          (foldBands r d r.bands).value.count*min r.grid (foldBands r d r.bands).value.windows+
            (foldBands r d r.bands).value.count*Ceil (r.i*r.grid) r.low)=true := by
    simpa only [step,Bool.and_eq_true] using h
  have hd := of_decide_eq_true hh.2
  exact ⟨fold_good hh.1,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1⟩

#print axioms check_sound
#print axioms step_good
end JSP233.CleanupEval208
