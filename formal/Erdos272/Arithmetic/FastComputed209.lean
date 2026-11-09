module

public import Erdos272.Arithmetic.ComputedTotient209

@[expose] public section
namespace JSP233.FastComputed209
set_option maxHeartbeats 0
def value (base factor : Nat → Nat) (fuel n : Nat) : Nat :=
  if n ≤ 32753 then base n else
  match fuel with
  | 0 => 0
  | k + 1 =>
    match factor n with
    | 0 => n - 1
    | p + 1 =>
      let m := n / (p + 1)
      (if p + 1 ∣ m then p + 1 else p) * value base factor k m

theorem value_eq (base factor : Nat → Nat) (fuel n : Nat) :
    value base factor fuel n = ComputedTotient209.value base factor fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    by_cases hn : n ≤ 32753
    · simp only [value, ComputedTotient209.value, if_pos hn]
    · simp only [value, ComputedTotient209.value, if_neg hn]
      cases hp : factor n with
      | zero => simp
      | succ p =>
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, ih]

#print axioms value_eq
end JSP233.FastComputed209
