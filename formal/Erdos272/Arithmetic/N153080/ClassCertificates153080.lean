module

public import Erdos272.Arithmetic.N155716.ClassCertificates155716

@[expose] public section

namespace JSP233.ClassCertificates153080
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cert11_40 : Certificate 11 40 6 := by
  decide +kernel

theorem cert11_62 : Certificate 11 62 10 := by
  decide +kernel

theorem cert11_88 : Certificate 11 88 17 := by
  decide +kernel

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(40,20),(62,31),(88,44)] else
    if p=3 then [(40,6),(62,10)] else
    if p=5 then [(40,2),(62,4)] else if p=11 then [(40,6),(62,10),(88,17)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates155716.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 21, 10), (2, 27, 13), (2, 32, 16), (2, 39, 19), (2, 40, 20), (2, 49, 24), (2, 62, 31), (2, 73, 36), (2, 88, 44),
    (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 11, 1), (3, 13, 2), (3, 14, 2), (3, 16, 2), (3, 17, 2), (3, 19, 3), (3, 22, 3), (3, 26, 4), (3, 31, 5), (3, 40, 6), (3, 49, 8), (3, 62, 10), (3, 73, 12), (3, 88, 14),
    (5, 23, 1), (5, 27, 1), (5, 40, 2), (5, 49, 2), (5, 62, 4), (5, 73, 4), (5, 88, 5),
    (7, 49, 1), (7, 62, 1), (7, 73, 2), (7, 88, 2),
    (11, 11, 1), (11, 13, 1), (11, 16, 1), (11, 17, 1), (11, 19, 1), (11, 20, 2), (11, 24, 2), (11, 40, 6), (11, 49, 8), (11, 62, 10), (11, 73, 13), (11, 88, 17)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(40,20),(62,31),(88,44)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact certificate_scale unit2 20
    · exact certificate_scale unit2 31
    · exact certificate_scale unit2 44
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(40,6),(62,10)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact certificate_mono (by decide : 36 ≤ 40) (le_refl 6) (certificate_scale unit3 6)
    · exact certificate_mono (by decide : 60 ≤ 62) (le_refl 10) (certificate_scale unit3 10)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(40,2),(62,4)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact certificate_scale cert5_20 2
    · exact certificate_mono (by decide : 60 ≤ 62) (le_refl 4)
        (certificate_scale ClassCertificates155716.cert5_30 2)
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(40,6),(62,10),(88,17)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact cert11_40
    · exact cert11_62
    · exact cert11_88
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates155716.class_basis_checked p v h
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

#print axioms cert11_40
#print axioms cert11_62
#print axioms cert11_88
#print axioms extras_checked
#print axioms class_basis_checked
#print axioms coverage
#print axioms selected_certificate
#print axioms selected_physical_count
end JSP233.ClassCertificates153080
