module

public import Erdos272.Arithmetic.N86412.ClassCertificates86412

@[expose] public section

namespace JSP233.ClassCertificates84364
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [] else if p=3 then [] else if p=5 then [] else if p=7 then [] else if p=11 then [] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates86412.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 23, 11), (2, 25, 12), (2, 26, 13), (2, 29, 14), (2, 31, 15), (2, 33, 16), (2, 34, 17), (2, 35, 17), (2, 37, 18), (2, 40, 20), (2, 44, 22), (2, 46, 23), (2, 51, 25), (2, 54, 27), (2, 56, 28), (2, 60, 30), (2, 66, 33), (2, 70, 35), (2, 75, 37), (2, 79, 39), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 23, 3), (3, 25, 4), (3, 27, 4), (3, 28, 4), (3, 29, 4), (3, 31, 5), (3, 34, 5), (3, 37, 6), (3, 40, 6), (3, 44, 7), (3, 46, 7), (3, 51, 8), (3, 54, 9), (3, 56, 9), (3, 60, 10), (3, 66, 11), (3, 70, 11), (3, 75, 12), (3, 79, 13), (5, 20, 1), (5, 21, 1), (5, 23, 1), (5, 24, 1), (5, 29, 1), (5, 31, 2), (5, 34, 2), (5, 37, 2), (5, 40, 2), (5, 44, 2), (5, 46, 2), (5, 51, 3), (5, 54, 3), (5, 56, 3), (5, 60, 4), (5, 66, 4), (5, 70, 4), (5, 75, 4), (5, 79, 4), (7, 44, 1), (7, 46, 1), (7, 51, 1), (7, 54, 1), (7, 56, 1), (7, 60, 1), (7, 66, 1), (7, 70, 2), (7, 75, 2), (7, 79, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 18, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 29, 3), (11, 31, 4), (11, 34, 4), (11, 37, 5), (11, 40, 6), (11, 44, 6), (11, 46, 7), (11, 51, 8), (11, 54, 9), (11, 56, 9), (11, 60, 11), (11, 66, 12), (11, 70, 14), (11, 75, 13), (11, 79, 15)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
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
  · exact ClassCertificates86412.class_basis_checked p v h
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
end JSP233.ClassCertificates84364
