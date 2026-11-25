module

public import Erdos272.Counting.N158375.ClassCount158375

@[expose] public section

namespace JSP233.ClassCountConcat158375
open ClassCount158375
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem window_count_add (p a n m : ℕ) :
    WindowCount p a (n+m) = WindowCount p a n+WindowCount p (a+n) m := by
  unfold WindowCount
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]

theorem certificate_add {p n m b c : ℕ}
    (h : Certificate p n b) (k : Certificate p m c) : Certificate p (n+m) (b+c) := by
  intro r hr
  rw [window_count_add]
  exact Nat.add_le_add (certificate_lower h r) (certificate_lower k (r+n))

theorem certificate_scale {p n b : ℕ} (h : Certificate p n b) (k : ℕ) :
    Certificate p (k*n) (k*b) := by
  induction k with
  | zero => intro r hr; simp [WindowCount]
  | succ k ih => simpa only [Nat.succ_mul] using certificate_add ih h

#print axioms window_count_add
#print axioms certificate_add
#print axioms certificate_scale
end JSP233.ClassCountConcat158375
