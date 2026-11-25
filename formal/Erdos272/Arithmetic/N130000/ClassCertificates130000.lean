module

public import Erdos272.Arithmetic.N142758.ClassCertificates142758
public import Erdos272.Counting.N130000.ClassCycle130000P11N28
public import Erdos272.Counting.N130000.ClassCycle130000P11N30
public import Erdos272.Counting.N130000.ClassCycle130000P11N36
public import Erdos272.Counting.N130000.ClassCycle130000P11N66
public import Erdos272.Counting.N130000.ClassCycle130000P11N97
public import Erdos272.Counting.N130000.ClassCycle130000P11N109

@[expose] public section

namespace JSP233.ClassCertificates130000
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(34,17),(56,28),(57,28),(66,33),(92,46),(94,47),(97,48),(103,51),(109,54)] else if p=3 then [(36,6),(66,11),(97,16),(103,17),(109,18)] else if p=5 then [(30,2)] else if p=7 then [] else if p=11 then [(28,3),(30,4),(36,5),(66,12),(97,20),(103,20),(109,22)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates142758.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 21, 10), (2, 22, 11), (2, 23, 11), (2, 24, 12), (2, 25, 12), (2, 26, 13), (2, 27, 13), (2, 29, 14), (2, 30, 15), (2, 33, 16), (2, 34, 17), (2, 35, 17), (2, 36, 18), (2, 37, 18), (2, 39, 19), (2, 40, 20), (2, 41, 20), (2, 42, 21), (2, 43, 21), (2, 45, 22), (2, 49, 24), (2, 50, 25), (2, 53, 26), (2, 56, 28), (2, 57, 28), (2, 58, 29), (2, 62, 31), (2, 66, 33), (2, 68, 34), (2, 70, 35), (2, 75, 37), (2, 77, 38), (2, 79, 39), (2, 83, 41), (2, 85, 42), (2, 87, 43), (2, 92, 46), (2, 94, 47), (2, 97, 48), (2, 103, 51), (2, 109, 54), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 22, 3), (3, 24, 4), (3, 25, 4), (3, 26, 4), (3, 27, 4), (3, 28, 4), (3, 30, 5), (3, 31, 5), (3, 33, 5), (3, 34, 5), (3, 35, 5), (3, 36, 6), (3, 37, 6), (3, 39, 6), (3, 41, 6), (3, 42, 7), (3, 43, 7), (3, 45, 7), (3, 49, 8), (3, 50, 8), (3, 53, 8), (3, 56, 9), (3, 57, 9), (3, 58, 9), (3, 62, 10), (3, 66, 11), (3, 68, 11), (3, 70, 11), (3, 75, 12), (3, 77, 12), (3, 79, 13), (3, 83, 13), (3, 85, 14), (3, 87, 14), (3, 92, 15), (3, 94, 15), (3, 97, 16), (3, 103, 17), (3, 109, 18), (5, 20, 1), (5, 21, 1), (5, 23, 1), (5, 24, 1), (5, 25, 1), (5, 26, 1), (5, 28, 1), (5, 29, 1), (5, 30, 2), (5, 32, 2), (5, 33, 2), (5, 34, 2), (5, 36, 2), (5, 37, 2), (5, 39, 2), (5, 41, 2), (5, 42, 2), (5, 43, 2), (5, 45, 2), (5, 49, 2), (5, 50, 3), (5, 53, 3), (5, 56, 3), (5, 57, 3), (5, 58, 3), (5, 62, 4), (5, 66, 4), (5, 68, 4), (5, 70, 4), (5, 75, 4), (5, 77, 4), (5, 79, 4), (5, 83, 5), (5, 85, 5), (5, 87, 5), (5, 92, 6), (5, 94, 6), (5, 97, 6), (5, 103, 6), (5, 109, 6), (7, 42, 1), (7, 43, 1), (7, 45, 1), (7, 49, 1), (7, 50, 1), (7, 53, 1), (7, 56, 1), (7, 57, 1), (7, 58, 1), (7, 62, 1), (7, 66, 1), (7, 68, 1), (7, 70, 2), (7, 75, 2), (7, 77, 2), (7, 79, 2), (7, 83, 2), (7, 85, 2), (7, 87, 2), (7, 92, 2), (7, 94, 2), (7, 97, 2), (7, 103, 2), (7, 109, 2), (11, 10, 1), (11, 11, 1), (11, 12, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 18, 1), (11, 19, 1), (11, 20, 2), (11, 21, 2), (11, 22, 2), (11, 23, 2), (11, 24, 2), (11, 25, 2), (11, 26, 2), (11, 28, 3), (11, 30, 4), (11, 34, 4), (11, 36, 5), (11, 37, 5), (11, 39, 5), (11, 41, 6), (11, 42, 7), (11, 43, 7), (11, 45, 6), (11, 49, 8), (11, 50, 8), (11, 53, 8), (11, 56, 9), (11, 57, 9), (11, 58, 9), (11, 62, 10), (11, 66, 12), (11, 68, 12), (11, 70, 14), (11, 75, 13), (11, 77, 14), (11, 79, 15), (11, 83, 15), (11, 85, 17), (11, 87, 16), (11, 92, 18), (11, 94, 19), (11, 97, 20), (11, 103, 20), (11, 109, 22)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(34,17),(56,28),(57,28),(66,33),(92,46),(94,47),(97,48),(103,51),(109,54)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 34 ≤ 34) (le_refl 17) (certificate_scale unit2 17)
    · exact certificate_mono (by decide : 56 ≤ 56) (le_refl 28) (certificate_scale unit2 28)
    · exact certificate_mono (by decide : 56 ≤ 57) (le_refl 28) (certificate_scale unit2 28)
    · exact certificate_mono (by decide : 66 ≤ 66) (le_refl 33) (certificate_scale unit2 33)
    · exact certificate_mono (by decide : 92 ≤ 92) (le_refl 46) (certificate_scale unit2 46)
    · exact certificate_mono (by decide : 94 ≤ 94) (le_refl 47) (certificate_scale unit2 47)
    · exact certificate_mono (by decide : 96 ≤ 97) (le_refl 48) (certificate_scale unit2 48)
    · exact certificate_mono (by decide : 102 ≤ 103) (le_refl 51) (certificate_scale unit2 51)
    · exact certificate_mono (by decide : 108 ≤ 109) (le_refl 54) (certificate_scale unit2 54)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(36,6),(66,11),(97,16),(103,17),(109,18)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 36 ≤ 36) (le_refl 6) (certificate_scale unit3 6)
    · exact certificate_mono (by decide : 66 ≤ 66) (le_refl 11) (certificate_scale unit3 11)
    · exact certificate_mono (by decide : 96 ≤ 97) (le_refl 16) (certificate_scale unit3 16)
    · exact certificate_mono (by decide : 102 ≤ 103) (le_refl 17) (certificate_scale unit3 17)
    · exact certificate_mono (by decide : 108 ≤ 109) (le_refl 18) (certificate_scale unit3 18)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(30,2)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl
    · exact certificate_mono (by decide : 30 ≤ 30) (by decide : 2 ≤ 2) (certificate_scale ClassCertificates155716.cert5_30 1)
  by_cases h7 : p=7
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(28,3),(30,4),(36,5),(66,12),(97,20),(103,20),(109,22)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ClassCycle130000P11N28.cert11_28
    · exact ClassCycle130000P11N30.cert11_30
    · exact ClassCycle130000P11N36.cert11_36
    · exact ClassCycle130000P11N66.cert11_66
    · exact ClassCycle130000P11N97.cert11_97
    · exact certificate_mono (by decide : 101 ≤ 103) (by decide : 20 ≤ 20) (certificate_add (ClassCertificates142758.class_basis_checked 11 (91,19) (by decide)) (ClassCertificates142758.class_basis_checked 11 (10,1) (by decide)))
    · exact ClassCycle130000P11N109.cert11_109
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates142758.class_basis_checked p v h
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
end JSP233.ClassCertificates130000
