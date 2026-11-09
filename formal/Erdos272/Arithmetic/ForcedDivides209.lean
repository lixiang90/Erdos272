module

public import Erdos272.Arithmetic.ForcedCheck209
public import Erdos272.Arithmetic.ComputedTotient209

@[expose] public section
namespace JSP233.ForcedDivides209
set_option maxHeartbeats 0
def check (factor : Nat → Nat) (lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let n := lo + k
    ForcedCheck209.withNat (factor n) (fun p => decide (p = 0 ∨ p ∣ n) && check factor lo k)
theorem check_eq (factor : Nat → Nat) (lo len : Nat) :
    check factor lo len = ComputedTotient209.checkDivides factor lo len := by
  induction len with
  | zero => rfl
  | succ k ih => simp only [check, ForcedCheck209.withNat_eq, ComputedTotient209.checkDivides, ih]
theorem check_sound {factor : Nat → Nat} {lo len n : Nat}
    (hc : check factor lo len = true) (hlo : lo ≤ n) (hhi : n < lo + len)
    (hp0 : factor n ≠ 0) : factor n ∣ n := by
  rw [check_eq] at hc
  exact ComputedTotient209.checkDivides_sound hc hlo hhi hp0
#print axioms check_eq
#print axioms check_sound
end JSP233.ForcedDivides209
