module

public import Erdos272.Arithmetic.N158375.ClassCertificates158375A
public import Erdos272.Arithmetic.N158375.ClassCertificates158375B
public import Erdos272.Arithmetic.N158375.ClassCertificates158375C

@[expose] public section

namespace JSP233.ClassCertificates158375
open ClassCount158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then Basis2 else if p=3 then Basis3 else if p=5 then Basis5 else
    if p=7 then Basis7 else if p=11 then Basis11 else []

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 22, 11), (2, 25, 12), (2, 26, 13), (2, 28, 14), (2, 30, 15), (2, 32, 16), (2, 36, 18), (2, 38, 19), (2, 41, 20), (2, 43, 21), (2, 48, 24), (2, 51, 25), (2, 58, 29), (2, 59, 29), (2, 64, 32), (2, 70, 35), (2, 73, 36), (2, 82, 41), (2, 83, 41), (2, 87, 43),
    (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 20, 3), (3, 21, 3), (3, 23, 3), (3, 25, 4), (3, 26, 4), (3, 30, 5), (3, 31, 5), (3, 41, 6), (3, 43, 7), (3, 48, 8), (3, 51, 8), (3, 58, 9), (3, 59, 9), (3, 64, 10), (3, 70, 11), (3, 73, 12), (3, 82, 13), (3, 83, 13), (3, 87, 14),
    (5, 20, 1), (5, 21, 1), (5, 22, 1), (5, 25, 1), (5, 26, 1), (5, 41, 2), (5, 43, 2), (5, 48, 2), (5, 51, 3), (5, 58, 3), (5, 59, 3), (5, 64, 4), (5, 70, 4), (5, 73, 4), (5, 82, 5), (5, 83, 5), (5, 87, 5),
    (7, 43, 1), (7, 48, 1), (7, 51, 1), (7, 58, 1), (7, 59, 1), (7, 64, 1), (7, 70, 2), (7, 73, 2), (7, 82, 2), (7, 83, 2), (7, 87, 2),
    (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 19, 1), (11, 20, 2), (11, 22, 2), (11, 23, 2), (11, 41, 6), (11, 43, 7), (11, 48, 8), (11, 51, 8), (11, 58, 9), (11, 59, 9), (11, 64, 11), (11, 70, 14), (11, 73, 13), (11, 82, 15), (11, 83, 15), (11, 87, 16)]

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    exact checked2 v hv
  by_cases h3 : p=3
  · subst p
    exact checked3 v hv
  by_cases h5 : p=5
  · subst p
    exact checked5 v hv
  by_cases h7 : p=7
  · subst p
    exact checked7 v hv
  by_cases h11 : p=11
  · subst p
    exact checked11 v hv
  have he : ClassBasis p = [] := by simp only [ClassBasis, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

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
end JSP233.ClassCertificates158375
