module

public import Erdos272.Arithmetic.N88404.ClassCertificates88404

@[expose] public section

namespace JSP233.ClassCertificates86412
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(72,36)] else if p=3 then [(72,12)] else if p=5 then [] else if p=7 then [] else if p=11 then [] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates88404.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 22, 11), (2, 23, 11), (2, 24, 12), (2, 26, 13), (2, 27, 13), (2, 29, 14), (2, 30, 15), (2, 31, 15), (2, 32, 16), (2, 33, 16), (2, 35, 17), (2, 36, 18), (2, 38, 19), (2, 39, 19), (2, 41, 20), (2, 43, 21), (2, 45, 22), (2, 47, 23), (2, 50, 25), (2, 52, 26), (2, 55, 27), (2, 58, 29), (2, 61, 30), (2, 64, 32), (2, 68, 34), (2, 72, 36), (2, 77, 38), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 22, 3), (3, 23, 3), (3, 24, 4), (3, 26, 4), (3, 28, 4), (3, 29, 4), (3, 30, 5), (3, 31, 5), (3, 32, 5), (3, 33, 5), (3, 35, 5), (3, 36, 6), (3, 38, 6), (3, 39, 6), (3, 41, 6), (3, 43, 7), (3, 45, 7), (3, 47, 7), (3, 50, 8), (3, 52, 8), (3, 55, 9), (3, 58, 9), (3, 61, 10), (3, 64, 10), (3, 68, 11), (3, 72, 12), (3, 77, 12), (5, 20, 1), (5, 21, 1), (5, 22, 1), (5, 23, 1), (5, 29, 1), (5, 30, 2), (5, 31, 2), (5, 32, 2), (5, 33, 2), (5, 35, 2), (5, 36, 2), (5, 38, 2), (5, 39, 2), (5, 41, 2), (5, 43, 2), (5, 45, 2), (5, 47, 2), (5, 50, 3), (5, 52, 3), (5, 55, 3), (5, 58, 3), (5, 61, 4), (5, 64, 4), (5, 68, 4), (5, 72, 4), (5, 77, 4), (7, 43, 1), (7, 45, 1), (7, 47, 1), (7, 50, 1), (7, 52, 1), (7, 55, 1), (7, 58, 1), (7, 61, 1), (7, 64, 1), (7, 68, 1), (7, 72, 2), (7, 77, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 18, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 29, 3), (11, 30, 4), (11, 31, 4), (11, 32, 3), (11, 33, 3), (11, 35, 4), (11, 36, 5), (11, 38, 5), (11, 39, 5), (11, 41, 6), (11, 43, 7), (11, 45, 6), (11, 47, 7), (11, 50, 8), (11, 52, 8), (11, 55, 9), (11, 58, 9), (11, 61, 11), (11, 64, 11), (11, 68, 12), (11, 72, 13), (11, 77, 14)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(72,36)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 72 ≤ 72) (le_refl 36) (certificate_scale unit2 36)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(72,12)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 72 ≤ 72) (le_refl 12) (certificate_scale unit3 12)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h7 : p=7
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h11 : p=11
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates88404.class_basis_checked p v h
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
end JSP233.ClassCertificates86412
