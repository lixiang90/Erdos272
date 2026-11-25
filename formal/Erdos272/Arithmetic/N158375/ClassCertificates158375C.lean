module

public import Erdos272.Counting.N158375.ClassCount158375

@[expose] public section

namespace JSP233.ClassCertificates158375C
open ClassCount158375
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Basis5 : List (ℕ × ℕ) :=
  [(20, 1), (41, 2), (51, 3), (64, 4), (82, 5)]

theorem cert5_20 : Certificate 5 20 1 := by
  decide +kernel
#print axioms cert5_20

theorem cert5_41 : Certificate 5 41 2 := by
  decide +kernel
#print axioms cert5_41

theorem cert5_51 : Certificate 5 51 3 := by
  decide +kernel
#print axioms cert5_51

theorem cert5_64 : Certificate 5 64 4 := by
  decide +kernel
#print axioms cert5_64

theorem cert5_82 : Certificate 5 82 5 := by
  decide +kernel
#print axioms cert5_82

theorem checked5 : ∀ v ∈ Basis5, Certificate 5 v.1 v.2 := by
  intro v hv
  simp only [Basis5, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact cert5_20
  · exact cert5_41
  · exact cert5_51
  · exact cert5_64
  · exact cert5_82

#print axioms checked5

def Basis7 : List (ℕ × ℕ) :=
  [(43, 1), (70, 2)]

theorem cert7_43 : Certificate 7 43 1 := by
  decide +kernel
#print axioms cert7_43

theorem cert7_70 : Certificate 7 70 2 := by
  decide +kernel
#print axioms cert7_70

theorem checked7 : ∀ v ∈ Basis7, Certificate 7 v.1 v.2 := by
  intro v hv
  simp only [Basis7, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact cert7_43
  · exact cert7_70

#print axioms checked7

def Basis11 : List (ℕ × ℕ) :=
  [(10, 1), (20, 2), (41, 6), (43, 7), (48, 8), (58, 9), (64, 11), (70, 14), (82, 15), (87, 16)]

theorem cert11_10 : Certificate 11 10 1 := by
  decide +kernel
#print axioms cert11_10

theorem cert11_20 : Certificate 11 20 2 := by
  decide +kernel
#print axioms cert11_20

theorem cert11_41 : Certificate 11 41 6 := by
  decide +kernel
#print axioms cert11_41

theorem cert11_43 : Certificate 11 43 7 := by
  decide +kernel
#print axioms cert11_43

theorem cert11_48 : Certificate 11 48 8 := by
  decide +kernel
#print axioms cert11_48

theorem cert11_58 : Certificate 11 58 9 := by
  decide +kernel
#print axioms cert11_58

theorem cert11_64 : Certificate 11 64 11 := by
  decide +kernel
#print axioms cert11_64

theorem cert11_70 : Certificate 11 70 14 := by
  decide +kernel
#print axioms cert11_70

theorem cert11_82 : Certificate 11 82 15 := by
  decide +kernel
#print axioms cert11_82

theorem cert11_87 : Certificate 11 87 16 := by
  decide +kernel
#print axioms cert11_87

theorem checked11 : ∀ v ∈ Basis11, Certificate 11 v.1 v.2 := by
  intro v hv
  simp only [Basis11, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert11_10
  · exact cert11_20
  · exact cert11_41
  · exact cert11_43
  · exact cert11_48
  · exact cert11_58
  · exact cert11_64
  · exact cert11_70
  · exact cert11_82
  · exact cert11_87

#print axioms checked11

end JSP233.ClassCertificates158375C
