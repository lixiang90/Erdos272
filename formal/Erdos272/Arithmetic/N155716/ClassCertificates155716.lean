module

public import Erdos272.Arithmetic.N158375.ClassCertificates158375
public import Erdos272.Counting.N158375.ClassCountConcat158375

@[expose] public section

namespace JSP233.ClassCertificates155716
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cert5_30 : Certificate 5 30 2 := by
  decide +kernel

theorem cert11_69 : Certificate 11 69 12 := by
  decide +kernel

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(16,8),(50,25),(69,34)] else
    if p=3 then [(24,4),(69,11)] else
    if p=5 then [(50,3)] else if p=11 then [(69,12)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates158375.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 20, 10), (2, 22, 11), (2, 25, 12), (2, 30, 15), (2, 36, 18), (2, 41, 20), (2, 50, 25), (2, 58, 29), (2, 69, 34), (2, 82, 41),
    (3, 6, 1), (3, 7, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 18, 3), (3, 20, 3), (3, 21, 3), (3, 24, 4), (3, 29, 4), (3, 41, 6), (3, 50, 8), (3, 58, 9), (3, 69, 11), (3, 82, 13),
    (5, 20, 1), (5, 21, 1), (5, 25, 1), (5, 41, 2), (5, 50, 3), (5, 58, 3), (5, 69, 4), (5, 82, 5),
    (7, 50, 1), (7, 58, 1), (7, 69, 1), (7, 82, 2),
    (11, 10, 1), (11, 11, 1), (11, 13, 1), (11, 16, 1), (11, 19, 1), (11, 20, 2), (11, 22, 2), (11, 41, 6), (11, 50, 8), (11, 58, 9), (11, 69, 12), (11, 82, 15)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(16,8),(50,25),(69,34)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact certificate_scale unit2 8
    · exact certificate_scale unit2 25
    · exact certificate_mono (by decide : 68 ≤ 69) (le_refl 34) (certificate_scale unit2 34)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(24,4),(69,11)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact certificate_scale unit3 4
    · exact certificate_mono (by decide : 66 ≤ 69) (le_refl 11) (certificate_scale unit3 11)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(50,3)] : List (ℕ × ℕ)) at hv
    rcases List.mem_singleton.mp hv with rfl
    exact certificate_add cert5_30 cert5_20
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(69,12)] : List (ℕ × ℕ)) at hv
    rcases List.mem_singleton.mp hv with rfl
    exact cert11_69
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates158375.class_basis_checked p v h
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

#print axioms cert5_30
#print axioms cert11_69
#print axioms extras_checked
#print axioms class_basis_checked
#print axioms coverage
#print axioms selected_certificate
#print axioms selected_physical_count
end JSP233.ClassCertificates155716
