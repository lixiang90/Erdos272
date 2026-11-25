module

public import Erdos272.Counting.N158375.ClassCountConcat158375

@[expose] public section

namespace JSP233.ClassCertificates158375A
open ClassCount158375 ClassCountConcat158375
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Basis2 : List (ℕ × ℕ) :=
  [(2, 1), (4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (14, 7), (17, 8), (18, 9), (20, 10), (22, 11), (25, 12), (26, 13), (28, 14), (30, 15), (32, 16), (36, 18), (38, 19), (41, 20), (43, 21), (48, 24), (51, 25), (58, 29), (64, 32), (70, 35), (73, 36), (82, 41), (87, 43)]

theorem unit2 : Certificate 2 2 1 := by
  decide +kernel

theorem bounds2 : ∀ v ∈ Basis2, v.2*2 ≤ v.1 := by
  decide +kernel

theorem checked2 : ∀ v ∈ Basis2, Certificate 2 v.1 v.2 := by
  intro v hv
  have h := certificate_scale unit2 v.2
  exact certificate_mono (bounds2 v hv) (by simp) h

#print axioms unit2
#print axioms bounds2

#print axioms checked2

end JSP233.ClassCertificates158375A
