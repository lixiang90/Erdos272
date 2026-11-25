module

public import Erdos272.Arithmetic.N151879.ClassCertificates151879

@[expose] public section

namespace JSP233.ClassCertificates150465
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cert11_35 : Certificate 11 35 4 := by decide +kernel
#print axioms cert11_35

theorem cert11_79 : Certificate 11 79 15 := by decide +kernel
#print axioms cert11_79

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(45,22),(52,26),(79,39)] else if p=3 then [(79,13)] else if p=5 then [(35,2)] else if p=7 then [] else if p=11 then [(35,4),(79,15)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates151879.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 23, 11), (2, 27, 13), (2, 31, 15), (2, 35, 17), (2, 38, 19), (2, 39, 19), (2, 45, 22), (2, 52, 26), (2, 61, 30), (2, 69, 34), (2, 79, 39), (2, 87, 43), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 18, 3), (3, 20, 3), (3, 22, 3), (3, 25, 4), (3, 28, 4), (3, 31, 5), (3, 35, 5), (3, 39, 6), (3, 45, 7), (3, 52, 8), (3, 61, 10), (3, 69, 11), (3, 79, 13), (3, 87, 14), (5, 20, 1), (5, 21, 1), (5, 24, 1), (5, 27, 1), (5, 35, 2), (5, 39, 2), (5, 45, 2), (5, 52, 3), (5, 61, 4), (5, 69, 4), (5, 79, 4), (5, 87, 5), (7, 45, 1), (7, 52, 1), (7, 61, 1), (7, 69, 1), (7, 79, 2), (7, 87, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 16, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 23, 2), (11, 35, 4), (11, 39, 5), (11, 45, 6), (11, 52, 8), (11, 61, 11), (11, 69, 12), (11, 79, 15), (11, 87, 16)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(45,22),(52,26),(79,39)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact certificate_mono (by decide : 44 ≤ 45) (le_refl 22) (certificate_scale unit2 22)
    · exact certificate_mono (by decide : 52 ≤ 52) (le_refl 26) (certificate_scale unit2 26)
    · exact certificate_mono (by decide : 78 ≤ 79) (le_refl 39) (certificate_scale unit2 39)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(79,13)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 78 ≤ 79) (le_refl 13) (certificate_scale unit3 13)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(35,2)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 30 ≤ 35) (by decide : 2 ≤ 2) ClassCertificates155716.cert5_30
  by_cases h7 : p=7
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(35,4),(79,15)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact cert11_35
    · exact cert11_79
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates151879.class_basis_checked p v h
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

#print axioms extras_checked
#print axioms class_basis_checked
#print axioms coverage
#print axioms selected_certificate
#print axioms selected_physical_count
end JSP233.ClassCertificates150465
