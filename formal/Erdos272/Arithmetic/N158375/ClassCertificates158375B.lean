module

public import Erdos272.Counting.N158375.ClassCountConcat158375

@[expose] public section

namespace JSP233.ClassCertificates158375B
open ClassCount158375 ClassCountConcat158375
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Basis3 : List (ℕ × ℕ) :=
  [(6, 1), (12, 2), (18, 3), (25, 4), (30, 5), (41, 6), (43, 7), (48, 8), (58, 9), (64, 10), (70, 11), (73, 12), (82, 13), (87, 14)]

theorem unit3 : Certificate 3 6 1 := by
  decide +kernel

theorem bounds3 : ∀ v ∈ Basis3, v.2*6 ≤ v.1 := by
  decide +kernel

theorem checked3 : ∀ v ∈ Basis3, Certificate 3 v.1 v.2 := by
  intro v hv
  have h := certificate_scale unit3 v.2
  exact certificate_mono (bounds3 v hv) (by simp) h

#print axioms unit3
#print axioms bounds3

#print axioms checked3

end JSP233.ClassCertificates158375B
