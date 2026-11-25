module

public import Erdos272.Arithmetic.N109474.ClassCertificates109474

@[expose] public section

namespace JSP233.ClassCertificates94488
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(74,37)] else if p=3 then [] else if p=5 then [] else if p=7 then [] else if p=11 then [] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates109474.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 22, 11), (2, 23, 11), (2, 24, 12), (2, 25, 12), (2, 26, 13), (2, 27, 13), (2, 28, 14), (2, 29, 14), (2, 30, 15), (2, 31, 15), (2, 32, 16), (2, 33, 16), (2, 35, 17), (2, 36, 18), (2, 37, 18), (2, 38, 19), (2, 41, 20), (2, 43, 21), (2, 44, 22), (2, 45, 22), (2, 46, 23), (2, 49, 24), (2, 51, 25), (2, 52, 26), (2, 53, 26), (2, 54, 27), (2, 56, 28), (2, 57, 28), (2, 58, 29), (2, 60, 30), (2, 61, 30), (2, 63, 31), (2, 64, 32), (2, 67, 33), (2, 68, 34), (2, 70, 35), (2, 74, 37), (2, 75, 37), (2, 76, 38), (2, 79, 39), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 22, 3), (3, 23, 3), (3, 24, 4), (3, 25, 4), (3, 26, 4), (3, 27, 4), (3, 28, 4), (3, 30, 5), (3, 31, 5), (3, 32, 5), (3, 33, 5), (3, 35, 5), (3, 36, 6), (3, 37, 6), (3, 38, 6), (3, 41, 6), (3, 43, 7), (3, 44, 7), (3, 45, 7), (3, 46, 7), (3, 49, 8), (3, 51, 8), (3, 52, 8), (3, 53, 8), (3, 54, 9), (3, 56, 9), (3, 57, 9), (3, 58, 9), (3, 60, 10), (3, 61, 10), (3, 63, 10), (3, 64, 10), (3, 67, 11), (3, 68, 11), (3, 70, 11), (3, 74, 12), (3, 75, 12), (3, 76, 12), (3, 79, 13), (5, 20, 1), (5, 21, 1), (5, 22, 1), (5, 23, 1), (5, 24, 1), (5, 28, 1), (5, 30, 2), (5, 31, 2), (5, 32, 2), (5, 33, 2), (5, 35, 2), (5, 36, 2), (5, 37, 2), (5, 38, 2), (5, 41, 2), (5, 43, 2), (5, 44, 2), (5, 45, 2), (5, 46, 2), (5, 49, 2), (5, 51, 3), (5, 52, 3), (5, 53, 3), (5, 54, 3), (5, 56, 3), (5, 57, 3), (5, 58, 3), (5, 60, 4), (5, 61, 4), (5, 63, 4), (5, 64, 4), (5, 67, 4), (5, 68, 4), (5, 70, 4), (5, 74, 4), (5, 75, 4), (5, 76, 4), (5, 79, 4), (7, 43, 1), (7, 44, 1), (7, 45, 1), (7, 46, 1), (7, 49, 1), (7, 51, 1), (7, 52, 1), (7, 53, 1), (7, 54, 1), (7, 56, 1), (7, 57, 1), (7, 58, 1), (7, 60, 1), (7, 61, 1), (7, 63, 1), (7, 64, 1), (7, 67, 1), (7, 68, 1), (7, 70, 2), (7, 74, 2), (7, 75, 2), (7, 76, 2), (7, 79, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 18, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 22, 2), (11, 28, 3), (11, 30, 4), (11, 31, 4), (11, 32, 3), (11, 33, 3), (11, 35, 4), (11, 36, 5), (11, 37, 5), (11, 38, 5), (11, 41, 6), (11, 43, 7), (11, 44, 6), (11, 45, 6), (11, 46, 7), (11, 49, 8), (11, 51, 8), (11, 52, 8), (11, 53, 8), (11, 54, 9), (11, 56, 9), (11, 57, 9), (11, 58, 9), (11, 60, 11), (11, 61, 11), (11, 63, 10), (11, 64, 11), (11, 67, 12), (11, 68, 12), (11, 70, 14), (11, 74, 13), (11, 75, 13), (11, 76, 14), (11, 79, 15)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(74,37)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 74 ≤ 74) (le_refl 37) (certificate_scale unit2 37)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
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
  · exact ClassCertificates109474.class_basis_checked p v h
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
end JSP233.ClassCertificates94488
