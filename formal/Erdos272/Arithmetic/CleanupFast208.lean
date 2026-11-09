module

public import Erdos272.Arithmetic.CleanupMachine208

@[expose] public section
namespace JSP233.CleanupFast208
open CleanupMachine208
set_option maxHeartbeats 0
def Extinct (r : Row) (d : Nat) (b : Band) : Prop :=
  let B:=block b d
  r.low ≤ r.high ∧ b.E ≤ b.T ∧ 0<B ∧ b.T<b.U+B-3 ∧ r.high/d<b.T-b.E
instance (r : Row) (d : Nat) (b : Band) : Decidable (Extinct r d b) := by
  unfold Extinct;infer_instance
def bandValue (r : Row) (d : Nat) (b : Band) : BandValue :=
  if b.E ≤ 1 then bandZero else if Extinct r d b then bandZero else CleanupMachine208.bandValue r d b
def foldBands (r : Row) (d : Nat) : List Band → BandFold
  | [] => ⟨bandZero,true⟩
  | b::bs =>
    let v:=bandValue r d b
    let tail:=foldBands r d bs
    ⟨bandAdd v tail.value,decide (BandGood r d b v) && tail.good⟩

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
end JSP233.CleanupFast208
