module

public import Erdos272.Arithmetic.N118533.ClassCertificates118533
public import Erdos272.Counting.N109474.ClassCycle109474P11N60
public import Erdos272.Counting.N109474.ClassCycle109474P11N90

@[expose] public section

namespace JSP233.ClassCertificates109474
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(44,22),(46,23),(60,30),(86,43),(90,45)] else if p=3 then [(60,10),(90,15)] else if p=5 then [(60,4),(90,6)] else if p=7 then [] else if p=11 then [(60,11),(90,19)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates118533.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 22, 11), (2, 23, 11), (2, 24, 12), (2, 25, 12), (2, 26, 13), (2, 28, 14), (2, 29, 14), (2, 30, 15), (2, 31, 15), (2, 32, 16), (2, 33, 16), (2, 34, 17), (2, 35, 17), (2, 36, 18), (2, 38, 19), (2, 39, 19), (2, 40, 20), (2, 41, 20), (2, 44, 22), (2, 45, 22), (2, 46, 23), (2, 48, 24), (2, 49, 24), (2, 50, 25), (2, 52, 26), (2, 53, 26), (2, 55, 27), (2, 57, 28), (2, 59, 29), (2, 60, 30), (2, 63, 31), (2, 64, 32), (2, 66, 33), (2, 70, 35), (2, 71, 35), (2, 73, 36), (2, 77, 38), (2, 79, 39), (2, 81, 40), (2, 82, 41), (2, 86, 43), (2, 88, 44), (2, 90, 45), (2, 91, 45), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 22, 3), (3, 23, 3), (3, 25, 4), (3, 26, 4), (3, 28, 4), (3, 29, 4), (3, 30, 5), (3, 31, 5), (3, 32, 5), (3, 33, 5), (3, 34, 5), (3, 35, 5), (3, 36, 6), (3, 38, 6), (3, 39, 6), (3, 40, 6), (3, 41, 6), (3, 44, 7), (3, 45, 7), (3, 46, 7), (3, 48, 8), (3, 49, 8), (3, 50, 8), (3, 52, 8), (3, 53, 8), (3, 55, 9), (3, 57, 9), (3, 59, 9), (3, 60, 10), (3, 63, 10), (3, 64, 10), (3, 66, 11), (3, 70, 11), (3, 71, 11), (3, 73, 12), (3, 77, 12), (3, 79, 13), (3, 81, 13), (3, 82, 13), (3, 86, 14), (3, 88, 14), (3, 90, 15), (3, 91, 15), (5, 20, 1), (5, 21, 1), (5, 22, 1), (5, 24, 1), (5, 25, 1), (5, 27, 1), (5, 28, 1), (5, 30, 2), (5, 31, 2), (5, 33, 2), (5, 34, 2), (5, 35, 2), (5, 36, 2), (5, 38, 2), (5, 39, 2), (5, 40, 2), (5, 41, 2), (5, 44, 2), (5, 45, 2), (5, 46, 2), (5, 48, 2), (5, 49, 2), (5, 50, 3), (5, 52, 3), (5, 53, 3), (5, 55, 3), (5, 57, 3), (5, 59, 3), (5, 60, 4), (5, 63, 4), (5, 64, 4), (5, 66, 4), (5, 70, 4), (5, 71, 4), (5, 73, 4), (5, 77, 4), (5, 79, 4), (5, 81, 5), (5, 82, 5), (5, 86, 5), (5, 88, 5), (5, 90, 6), (5, 91, 6), (7, 44, 1), (7, 45, 1), (7, 46, 1), (7, 48, 1), (7, 49, 1), (7, 50, 1), (7, 52, 1), (7, 53, 1), (7, 55, 1), (7, 57, 1), (7, 59, 1), (7, 60, 1), (7, 63, 1), (7, 64, 1), (7, 66, 1), (7, 70, 2), (7, 71, 2), (7, 73, 2), (7, 77, 2), (7, 79, 2), (7, 81, 2), (7, 82, 2), (7, 86, 2), (7, 88, 2), (7, 90, 2), (7, 91, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 18, 1), (11, 19, 1), (11, 21, 2), (11, 22, 2), (11, 24, 2), (11, 25, 2), (11, 30, 4), (11, 31, 4), (11, 33, 3), (11, 34, 4), (11, 35, 4), (11, 36, 5), (11, 38, 5), (11, 39, 5), (11, 40, 6), (11, 41, 6), (11, 44, 6), (11, 45, 6), (11, 46, 7), (11, 48, 8), (11, 49, 8), (11, 50, 8), (11, 52, 8), (11, 53, 8), (11, 55, 9), (11, 57, 9), (11, 59, 9), (11, 60, 11), (11, 63, 10), (11, 64, 11), (11, 66, 12), (11, 70, 14), (11, 71, 14), (11, 73, 13), (11, 77, 14), (11, 79, 15), (11, 81, 15), (11, 82, 15), (11, 86, 16), (11, 88, 17), (11, 90, 19), (11, 91, 19)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(44,22),(46,23),(60,30),(86,43),(90,45)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 44 ≤ 44) (le_refl 22) (certificate_scale unit2 22)
    · exact certificate_mono (by decide : 46 ≤ 46) (le_refl 23) (certificate_scale unit2 23)
    · exact certificate_mono (by decide : 60 ≤ 60) (le_refl 30) (certificate_scale unit2 30)
    · exact certificate_mono (by decide : 86 ≤ 86) (le_refl 43) (certificate_scale unit2 43)
    · exact certificate_mono (by decide : 90 ≤ 90) (le_refl 45) (certificate_scale unit2 45)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(60,10),(90,15)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact certificate_mono (by decide : 60 ≤ 60) (le_refl 10) (certificate_scale unit3 10)
    · exact certificate_mono (by decide : 90 ≤ 90) (le_refl 15) (certificate_scale unit3 15)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(60,4),(90,6)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact certificate_mono (by decide : 60 ≤ 60) (by decide : 4 ≤ 4) (certificate_scale ClassCertificates155716.cert5_30 2)
    · exact certificate_mono (by decide : 90 ≤ 90) (by decide : 6 ≤ 6) (certificate_scale ClassCertificates155716.cert5_30 3)
  by_cases h7 : p=7
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(60,11),(90,19)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ClassCycle109474P11N60.cert11_60
    · exact ClassCycle109474P11N90.cert11_90
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates118533.class_basis_checked p v h
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
end JSP233.ClassCertificates109474
