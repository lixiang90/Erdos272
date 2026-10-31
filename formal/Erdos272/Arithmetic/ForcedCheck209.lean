import Erdos272.Arithmetic.MarkerSieve209
import Erdos272.Arithmetic.FrontierCheck209

/-! Kernel evaluation is call by name. Matching a natural argument before
continuing keeps successive numeric accumulator expressions from growing.
The optimized checkers are proved equal to the original specifications. -/
namespace JSP233.ForcedCheck209
set_option maxHeartbeats 0

def withNat {α : Sort _} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem withNat_eq {α : Sort _} (n : Nat) (f : Nat → α) : withNat n f = f n := by
  cases n <;> rfl

def checkMultiples (marked : Nat → Bool) (p : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | n, k + 1 => marked n && withNat (n + p) (fun n' => checkMultiples marked p n' k)

theorem checkMultiples_eq (marked : Nat → Bool) (p n k : Nat) :
    checkMultiples marked p n k = MarkerSieve209.checkMultiples marked p n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [checkMultiples, withNat_eq, MarkerSieve209.checkMultiples, ih]

def checkRow (marked : Nat → Bool) (H p : Nat) : Bool := checkMultiples marked p (2*p) (H/p-1)
def check (marked : Nat → Bool) (P : List Nat) (H : Nat) : Bool := P.all (checkRow marked H)

theorem check_eq (marked : Nat → Bool) (P : List Nat) (H : Nat) :
    check marked P H = MarkerSieve209.check marked P H := by
  unfold check MarkerSieve209.check
  apply congrArg P.all
  funext p
  exact checkMultiples_eq marked p (2*p) (H/p-1)

theorem checked_interval {marked : Nat → Bool} {p qlo len q : Nat}
    (hc : checkMultiples marked p (p * qlo) len = true)
    (hlo : qlo ≤ q) (hhi : q < qlo + len) : marked (p * q) = true := by
  rw [checkMultiples_eq] at hc
  exact MarkerSieve209.checked_interval hc hlo hhi

def checkFrom (a : Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | _, 0, f, u, fEnd, uEnd => decide (f = fEnd ∧ u = uEnd)
  | n, k + 1, f, u, fEnd, uEnd =>
    withNat (n + 1) (fun t =>
    withNat (a t) (fun ph =>
    withNat (f + FrontierCheck209.Grid * ph / t) (fun f' =>
    withNat (u + if t = 1 then 0 else ph) (fun u' =>
      decide (FrontierCheck209.Good t f' u') && checkFrom a t k f' u' fEnd uEnd))))

theorem checkFrom_eq (a : Nat → Nat) (n k f u fEnd uEnd : Nat) :
    checkFrom a n k f u fEnd uEnd = FrontierCheck209.checkFrom a n k f u fEnd uEnd := by
  induction k generalizing n f u with
  | zero => rfl
  | succ k ih => simp only [checkFrom, withNat_eq, FrontierCheck209.checkFrom, ih]

theorem checkFrom_sound (a : Nat → Nat) (k n f u fEnd uEnd : Nat)
    (hf : f = FrontierCheck209.massFloor a n) (hu : u = FrontierCheck209.triangle a n)
    (hc : checkFrom a n k f u fEnd uEnd = true) :
    (fEnd = FrontierCheck209.massFloor a (n + k) ∧ uEnd = FrontierCheck209.triangle a (n + k)) ∧
    ∀ t, n < t → t ≤ n + k → FrontierCheck209.Good t
      (FrontierCheck209.massFloor a t) (FrontierCheck209.triangle a t) := by
  rw [checkFrom_eq] at hc
  exact FrontierCheck209.checkFrom_sound a k n f u fEnd uEnd hf hu hc

#print axioms withNat_eq
#print axioms checkMultiples_eq
#print axioms checkFrom_eq
#print axioms checkFrom_sound
end JSP233.ForcedCheck209
