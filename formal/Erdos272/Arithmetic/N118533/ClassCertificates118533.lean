module

public import Erdos272.Arithmetic.N130000.ClassCertificates130000

@[expose] public section

namespace JSP233.ClassCertificates118533
open ClassCount158375
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (_p : ℕ) : List (ℕ × ℕ) := []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) := ClassCertificates130000.ClassBasis p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 23, 11), (2, 24, 12), (2, 25, 12), (2, 29, 14), (2, 30, 15), (2, 31, 15), (2, 35, 17), (2, 37, 18), (2, 41, 20), (2, 47, 23), (2, 48, 24), (2, 57, 28), (2, 66, 33), (2, 68, 34), (2, 79, 39), (2, 84, 42), (2, 94, 47), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 17, 2), (3, 19, 3), (3, 20, 3), (3, 23, 3), (3, 24, 4), (3, 28, 4), (3, 30, 5), (3, 31, 5), (3, 33, 5), (3, 35, 5), (3, 37, 6), (3, 41, 6), (3, 47, 7), (3, 48, 8), (3, 57, 9), (3, 66, 11), (3, 68, 11), (3, 79, 13), (3, 84, 14), (3, 94, 15), (5, 20, 1), (5, 21, 1), (5, 24, 1), (5, 25, 1), (5, 29, 1), (5, 31, 2), (5, 35, 2), (5, 37, 2), (5, 41, 2), (5, 47, 2), (5, 48, 2), (5, 57, 3), (5, 66, 4), (5, 68, 4), (5, 79, 4), (5, 84, 5), (5, 94, 6), (7, 47, 1), (7, 48, 1), (7, 57, 1), (7, 66, 1), (7, 68, 1), (7, 79, 2), (7, 84, 2), (7, 94, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 18, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 23, 2), (11, 24, 2), (11, 26, 2), (11, 31, 4), (11, 35, 4), (11, 37, 5), (11, 41, 6), (11, 47, 7), (11, 48, 8), (11, 57, 9), (11, 66, 12), (11, 68, 12), (11, 79, 15), (11, 84, 17), (11, 94, 19)]

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := ClassCertificates130000.class_basis_checked p v hv

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

#print axioms class_basis_checked
#print axioms coverage
#print axioms selected_certificate
#print axioms selected_physical_count
end JSP233.ClassCertificates118533
