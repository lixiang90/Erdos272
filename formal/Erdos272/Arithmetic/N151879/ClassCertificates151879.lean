module

public import Erdos272.Arithmetic.N153080.ClassCertificates153080

@[expose] public section

namespace JSP233.ClassCertificates151879
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cert7_42 : Certificate 7 42 1 := by
  decide +kernel

theorem cert11_37 : Certificate 11 37 5 := by
  decide +kernel

theorem cert11_42 : Certificate 11 42 7 := by
  decide +kernel

theorem cert11_61 : Certificate 11 61 11 := by
  decide +kernel

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(35,17),(42,21),(53,26),(61,30),(80,40)] else
    if p=3 then [(37,6),(42,7),(61,10),(80,13)] else
    if p=5 then [(37,2),(61,4),(80,5)] else
    if p=7 then [(42,1)] else
    if p=11 then [(37,5),(42,7),(61,11),(80,15)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates153080.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 23, 11), (2, 27, 13), (2, 31, 15), (2, 35, 17), (2, 37, 18), (2, 38, 19), (2, 42, 21), (2, 53, 26), (2, 61, 30), (2, 70, 35), (2, 80, 40), (2, 88, 44),
    (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 18, 3), (3, 20, 3), (3, 22, 3), (3, 25, 4), (3, 28, 4), (3, 31, 5), (3, 37, 6), (3, 42, 7), (3, 53, 8), (3, 61, 10), (3, 70, 11), (3, 80, 13), (3, 88, 14),
    (5, 20, 1), (5, 21, 1), (5, 24, 1), (5, 27, 1), (5, 37, 2), (5, 42, 2), (5, 53, 3), (5, 61, 4), (5, 70, 4), (5, 80, 5), (5, 88, 5),
    (7, 42, 1), (7, 53, 1), (7, 61, 1), (7, 70, 2), (7, 80, 2), (7, 88, 2),
    (11, 10, 1), (11, 11, 1), (11, 13, 1), (11, 14, 1), (11, 16, 1), (11, 17, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 24, 2), (11, 37, 5), (11, 42, 7), (11, 53, 8), (11, 61, 11), (11, 70, 14), (11, 80, 15), (11, 88, 17)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(35,17),(42,21),(53,26),(61,30),(80,40)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 34 ≤ 35) (le_refl 17) (certificate_scale unit2 17)
    · exact certificate_scale unit2 21
    · exact certificate_mono (by decide : 52 ≤ 53) (le_refl 26) (certificate_scale unit2 26)
    · exact certificate_mono (by decide : 60 ≤ 61) (le_refl 30) (certificate_scale unit2 30)
    · exact certificate_scale unit2 40
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(37,6),(42,7),(61,10),(80,13)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 36 ≤ 37) (le_refl 6) (certificate_scale unit3 6)
    · exact certificate_scale unit3 7
    · exact certificate_mono (by decide : 60 ≤ 61) (le_refl 10) (certificate_scale unit3 10)
    · exact certificate_mono (by decide : 78 ≤ 80) (le_refl 13) (certificate_scale unit3 13)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(37,2),(61,4),(80,5)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact certificate_mono (by decide : 30 ≤ 37) (le_refl 2) ClassCertificates155716.cert5_30
    · exact certificate_mono (by decide : 60 ≤ 61) (le_refl 4) (certificate_scale ClassCertificates155716.cert5_30 2)
    · exact certificate_add (certificate_scale ClassCertificates155716.cert5_30 2) cert5_20
  by_cases h7 : p=7
  · subst p
    change v ∈ ([(42,1)] : List (ℕ × ℕ)) at hv
    rcases List.mem_singleton.mp hv with rfl
    exact cert7_42
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(37,5),(42,7),(61,11),(80,15)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact cert11_37
    · exact cert11_42
    · exact cert11_61
    · exact certificate_add cert11_70 cert11_10
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates153080.class_basis_checked p v h
  · exact extras_checked p v h

theorem coverage : ∀ v ∈ Required,
    ∃ c ∈ ClassBasis v.1, c.1 ≤ v.2.1 ∧ v.2.2 ≤ c.2 := by
  decide +kernel

theorem selected_certificate {p n b : ℕ} (h : (p,n,b) ∈ Required) :
    Certificate p n b := by
  obtain ⟨c, hc, hn, hb⟩ := coverage (p,n,b) h
  exact certificate_mono hn hb (class_basis_checked p c hc)

theorem selected_physical_count {N low q p b : ℕ} (hq : 0 < q) (hlo : low ≤ N)
    (h : (p,low/(q*(q+1)),b) ∈ Required) : b ≤ (Steps N q p).card :=
  physical_interval_count hq hlo (selected_certificate h)

#print axioms cert7_42
#print axioms cert11_37
#print axioms cert11_42
#print axioms cert11_61
#print axioms extras_checked
#print axioms class_basis_checked
#print axioms coverage
#print axioms selected_certificate
#print axioms selected_physical_count
end JSP233.ClassCertificates151879
