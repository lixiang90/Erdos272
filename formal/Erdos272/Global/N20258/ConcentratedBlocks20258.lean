module

public import Erdos272.Global.N20258.ConcentratedCut20258
public import Erdos272.Arithmetic.N20258.ConcentratedCharge20258
public import Erdos272.Arithmetic.N20258.EndpointCover20258

@[expose] public section
namespace JSP233.ConcentratedBlocks20258
open StarCompletion ConcentratedCut20258 ConcentratedPrice20258 FirstSparseCut20258
open scoped BigOperators
set_option autoImplicit false

inductive Source
  | marked (p : Plan)
  | uniform (minimum : ℕ)
  deriving DecidableEq

def Source.minimum : Source → ℕ
  | .marked p => p.minimum | .uniform m => m

def Source.head (x : ℕ) : Source → ℕ
  | .marked p => p.head | .uniform m => min x (UniformNumeric84364.value m)

def Source.debt (n : ℕ) : Source → ℕ
  | .marked p => ConcentratedCharge20258.debt p n | .uniform _ => 0

def Source.Valid : Source → Prop
  | .marked p => p.Valid | .uniform m => 4≤m ∧ m≤549

instance (s : Source) : Decidable s.Valid := by cases s <;> unfold Source.Valid <;> infer_instance

structure Route where
  lower : ℕ
  upper : ℕ
  percent : ℕ
  source : Source
  deriving DecidableEq

def Route.block (r : Route) (a b : ℕ) : Block :=
  let u := min r.upper (b/12)
  let length := max 1 ((443*a/5000-17)/(u-1))
  let x := max (r.source.head 0) ((r.percent*b+99)/100)
  ⟨a,b,r.lower,u,length,x⟩

def Route.Good (r : Route) (a b : ℕ) : Prop :=
  let block := r.block a b
  block.Valid r.source.minimum (r.source.head block.price) (r.source.debt b)

instance (r : Route) (a b : ℕ) : Decidable (r.Good a b) := by unfold Route.Good; infer_instance

theorem upper {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    {r : Route} {a b : ℕ} (lo : a≤N) (hi : N≤b) (lower : r.lower≤m) (higher : m≤r.upper)
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (valid : r.source.Valid)
    (good : r.Good a b) : F.card≤B N := by
  let z := r.block a b
  have cap := good.2.2.1
  have pos := good.1
  have sparse := cut.sparse
  apply ConcentratedCut20258.upper (b:=z) lo hi lower (le_min higher (by omega)) legal cut good
  intro A hA bad sz
  cases hs : r.source with
  | marked p =>
    rw [hs] at valid sz
    exact ConcentratedCharge20258.family valid hA (by change 20258≤a at pos; omega)
      (by change b<2^16 at cap; omega) sz bad
  | uniform s =>
    rw [hs] at valid sz
    have prices (S : Finset ℤ) (hS : S∈A) : (Source.uniform s).head z.price≤(IntrinsicTriples208.Pool S).card :=
      (min_le_right ..).trans (UniformCardPool20258.pool_floor (by change b≤2^18; change b<2^16 at cap; omega)
        (hA.1 S hS) (bad S hS) valid.1 valid.2 (sz S hS) le_rfl)
    simpa only [Source.debt,Nat.add_zero,Finset.sum_const,smul_eq_mul,Nat.mul_comm _ A.card]
      using Finset.sum_le_sum prices

#print axioms upper
end JSP233.ConcentratedBlocks20258
