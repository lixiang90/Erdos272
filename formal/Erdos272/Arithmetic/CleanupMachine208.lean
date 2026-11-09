module

public import Lean.Elab.Tactic.Decide
public import Lean.Elab.Deriving.DecEq

@[expose] public section
namespace JSP233.CleanupMachine208
set_option maxHeartbeats 0
def gate (d : Nat) : Nat := if 2 ∣ d then 2 else if 3 ∣ d then 3 else if 5 ∣ d then 5 else if 7 ∣ d then 7 else 11
def Ceil (a b : Nat) : Nat := (a+b-1)/b
def Count (q C B : Nat) : Nat := if C ≤ q then (q-C)/B+1 else 0
def Tri (n : Nat) : Nat := n*(n-1)/2
def RightLeft (q J B : Nat) : Nat := (q-J+B-1)/B
def rightIndexCount (q A J B : Nat) : Nat := Count q A B-RightLeft q J B
def Last (C B hi : Nat) : Nat := C+(hi-C)/B*B
def maximum (A J B lo hi : Nat) : Nat :=
  max (rightIndexCount lo A J B) (if A ≤ hi ∧ lo ≤ Last A B hi then min (Count J A B) (Count hi A B) else 0)
def rightWeight (q A J B : Nat) : Nat :=
  rightIndexCount q A J B*(q+1)-B*(Tri (Count q A B)-Tri (RightLeft q J B))
def Full (A J B : Nat) : Nat := Count J A B*(J+1)-B*Tri (Count J A B)
def maximum_sum (A J B lo hi : Nat) : Nat :=
  max (rightWeight hi A J B) (if J ≤ hi ∧ lo ≤ Last J B hi then Full A J B else 0)
def Switch (K B h : Nat) : Nat := K+(h-1)*B
def maximum_combined (A K B h lo hi : Nat) : Nat :=
  max (if lo<Switch K B h then Count (min hi (Switch K B h-1)) A B else 0)
    (if Switch K B h ≤ hi then h+maximum A (K-1) B (max lo (Switch K B h)) hi else 0)
def WeightSum (q T E B V : Nat) : Nat :=
  let L:=Count q (T-E) B
  let O:=Count q (V-E) B
  V*O+((L-O)*(q+E)-B*(Tri L-Tri O))
def Correction (N d T E B : Nat) : Nat :=
  if T-E ≤ N/d ∧ (N/d-(T-E))%B=0 then (d-N%d)*T else 0
def Closed (N d T E B V : Nat) : Nat := d*WeightSum (N/d) T E B V-Correction N d T E B
structure Band where
  T : Nat
  E : Nat
  U : Nat
  b2 : Nat
  b3 : Nat
  b5 : Nat
  b7 : Nat
  b11 : Nat
  deriving DecidableEq
structure Row where
  grid : Nat
  low : Nat
  high : Nat
  i : Nat
  bands : List Band
  deriving DecidableEq
structure Totals where
  first : Nat
  second : Nat
  credit : Nat
  net : Nat
  light : Nat
  deriving DecidableEq
def zero : Totals := ⟨0,0,0,0,0⟩
def add (a b : Totals) : Totals :=
  ⟨a.first+b.first,a.second+b.second,a.credit+b.credit,a.net+b.net,a.light+b.light⟩
structure BandValue where
  count : Nat
  windows : Nat
  credit : Nat
  light : Nat
  deriving DecidableEq
def bandZero : BandValue := ⟨0,0,0,0⟩
def bandAdd (a b : BandValue) : BandValue :=
  ⟨a.count+b.count,a.windows+b.windows,a.credit+b.credit,a.light+b.light⟩
def block (b : Band) (d : Nat) : Nat :=
  match gate d with
  | 2 => b.b2 | 3 => b.b3 | 5 => b.b5 | 7 => b.b7 | _ => b.b11

def bandValue (r : Row) (d : Nat) (b : Band) : BandValue :=
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
  ⟨count,one+two,count*(b.T*r.grid/r.high),Closed r.high d b.T b.E B V⟩

def BandGood (r : Row) (d : Nat) (b : Band) (v : BandValue) : Prop :=
  let B:=block b d
  let V:=b.U+B-3
  let p:=gate d
  1 ≤ b.E ∧ b.E ≤ r.i ∧ b.E ≤ b.T ∧ b.T<b.U ∧ 2 ≤ B ∧ B ≤ b.T-b.E ∧ b.T<V ∧
    ((p-1)*(b.T-b.E+1-B) ≥ b.E ∨ p*B ≤ (p-1)*(b.T-b.E+1)) ∧
    (0<v.count → (b.T-b.E+1)*r.grid ≤ min r.grid v.windows*r.high)
instance (r : Row) (d : Nat) (b : Band) (v : BandValue) : Decidable (BandGood r d b v) := by
  unfold BandGood;infer_instance

structure BandFold where
  value : BandValue
  good : Bool
def foldBands (r : Row) (d : Nat) : List Band → BandFold
  | [] => ⟨bandZero,true⟩
  | b::bs =>
    let v:=bandValue r d b
    let tail:=foldBands r d bs
    ⟨bandAdd v tail.value,decide (BandGood r d b v) && tail.good⟩

structure Chunk where
  totals : Totals
  good : Bool
def step (r : Row) (d : Nat) : Chunk :=
  let b:=foldBands r d r.bands
  let Z:=min r.grid b.value.windows
  let first:=b.value.count*Z
  let second:=b.value.count*Ceil (r.i*r.grid) r.low
  ⟨⟨first,second,b.value.credit,first+second-b.value.credit,b.value.light⟩,
    b.good && decide (0<r.grid ∧ 0<r.low ∧ r.low ≤ r.high ∧ 0<d ∧ b.value.credit ≤ first+second)⟩

def run (r : Row) (start : Nat) : Nat → Chunk
  | 0 => ⟨zero,true⟩
  | n+1 =>
    let before:=run r start n
    let v:=step r (start+n)
    ⟨add before.totals v.totals,before.good && v.good⟩
def checkChunk (r : Row) (start len : Nat) (expected : Totals) : Bool :=
  let result:=run r start len
  result.good && decide (result.totals=expected)

#print axioms checkChunk
end JSP233.CleanupMachine208
