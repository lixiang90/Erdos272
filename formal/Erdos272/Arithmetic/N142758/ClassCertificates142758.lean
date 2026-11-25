module

public import Erdos272.Arithmetic.N150465.ClassCertificates150465
public import Erdos272.Counting.N142758.ClassCycle142758P11N31
public import Erdos272.Counting.N142758.ClassCycle142758P11N54
public import Erdos272.Counting.N142758.ClassCycle142758P11N68
public import Erdos272.Counting.N142758.ClassCycle142758P11N84
public import Erdos272.Counting.N142758.ClassCycle142758P11N91

@[expose] public section

namespace JSP233.ClassCertificates142758
open ClassCount158375 ClassCountConcat158375
open ClassCertificates158375A ClassCertificates158375B ClassCertificates158375C
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Extras (p : ℕ) : List (ℕ × ℕ) :=
  if p=2 then [(24,12),(47,23),(54,27),(68,34),(75,37),(76,38),(84,42),(91,45),(93,46)] else if p=3 then [(54,9),(68,11),(84,14),(91,15),(93,15)] else if p=5 then [(31,2),(33,2),(91,6),(93,6)] else if p=7 then [] else if p=11 then [(31,4),(33,3),(54,9),(68,12),(84,17),(91,19),(93,18)] else []

def ClassBasis (p : ℕ) : List (ℕ × ℕ) :=
  ClassCertificates150465.ClassBasis p ++ Extras p

def Required : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 1), (2, 3, 1), (2, 4, 2), (2, 5, 2), (2, 6, 3), (2, 7, 3), (2, 8, 4), (2, 9, 4), (2, 10, 5), (2, 11, 5), (2, 12, 6), (2, 13, 6), (2, 14, 7), (2, 15, 7), (2, 16, 8), (2, 17, 8), (2, 18, 9), (2, 19, 9), (2, 20, 10), (2, 22, 11), (2, 23, 11), (2, 24, 12), (2, 25, 12), (2, 26, 13), (2, 27, 13), (2, 28, 14), (2, 30, 15), (2, 31, 15), (2, 33, 16), (2, 36, 18), (2, 37, 18), (2, 38, 19), (2, 40, 20), (2, 41, 20), (2, 42, 21), (2, 43, 21), (2, 47, 23), (2, 49, 24), (2, 50, 25), (2, 53, 26), (2, 54, 27), (2, 58, 29), (2, 59, 29), (2, 63, 31), (2, 64, 32), (2, 68, 34), (2, 70, 35), (2, 75, 37), (2, 76, 38), (2, 82, 41), (2, 84, 42), (2, 91, 45), (2, 93, 46), (3, 6, 1), (3, 7, 1), (3, 8, 1), (3, 9, 1), (3, 10, 1), (3, 11, 1), (3, 12, 2), (3, 13, 2), (3, 14, 2), (3, 15, 2), (3, 16, 2), (3, 17, 2), (3, 18, 3), (3, 19, 3), (3, 20, 3), (3, 21, 3), (3, 22, 3), (3, 25, 4), (3, 27, 4), (3, 29, 4), (3, 30, 5), (3, 31, 5), (3, 33, 5), (3, 37, 6), (3, 38, 6), (3, 40, 6), (3, 42, 7), (3, 43, 7), (3, 47, 7), (3, 49, 8), (3, 50, 8), (3, 53, 8), (3, 54, 9), (3, 58, 9), (3, 59, 9), (3, 63, 10), (3, 64, 10), (3, 68, 11), (3, 70, 11), (3, 75, 12), (3, 76, 12), (3, 82, 13), (3, 84, 14), (3, 91, 15), (3, 93, 15), (5, 20, 1), (5, 21, 1), (5, 23, 1), (5, 25, 1), (5, 26, 1), (5, 27, 1), (5, 28, 1), (5, 31, 2), (5, 33, 2), (5, 37, 2), (5, 38, 2), (5, 40, 2), (5, 42, 2), (5, 43, 2), (5, 47, 2), (5, 49, 2), (5, 50, 3), (5, 53, 3), (5, 54, 3), (5, 58, 3), (5, 59, 3), (5, 63, 4), (5, 64, 4), (5, 68, 4), (5, 70, 4), (5, 75, 4), (5, 76, 4), (5, 82, 5), (5, 84, 5), (5, 91, 6), (5, 93, 6), (7, 42, 1), (7, 43, 1), (7, 47, 1), (7, 49, 1), (7, 50, 1), (7, 53, 1), (7, 54, 1), (7, 58, 1), (7, 59, 1), (7, 63, 1), (7, 64, 1), (7, 68, 1), (7, 70, 2), (7, 75, 2), (7, 76, 2), (7, 82, 2), (7, 84, 2), (7, 91, 2), (7, 93, 2), (11, 10, 1), (11, 11, 1), (11, 13, 1), (11, 14, 1), (11, 15, 1), (11, 16, 1), (11, 17, 1), (11, 19, 1), (11, 20, 2), (11, 22, 2), (11, 25, 2), (11, 31, 4), (11, 33, 3), (11, 37, 5), (11, 38, 5), (11, 40, 6), (11, 42, 7), (11, 43, 7), (11, 47, 7), (11, 49, 8), (11, 50, 8), (11, 53, 8), (11, 54, 9), (11, 58, 9), (11, 59, 9), (11, 63, 10), (11, 64, 11), (11, 68, 12), (11, 70, 14), (11, 75, 13), (11, 76, 14), (11, 82, 15), (11, 84, 17), (11, 91, 19), (11, 93, 18)]

theorem extras_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ Extras p) :
    Certificate p v.1 v.2 := by
  by_cases h2 : p=2
  · subst p
    change v ∈ ([(24,12),(47,23),(54,27),(68,34),(75,37),(76,38),(84,42),(91,45),(93,46)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 24 ≤ 24) (le_refl 12) (certificate_scale unit2 12)
    · exact certificate_mono (by decide : 46 ≤ 47) (le_refl 23) (certificate_scale unit2 23)
    · exact certificate_mono (by decide : 54 ≤ 54) (le_refl 27) (certificate_scale unit2 27)
    · exact certificate_mono (by decide : 68 ≤ 68) (le_refl 34) (certificate_scale unit2 34)
    · exact certificate_mono (by decide : 74 ≤ 75) (le_refl 37) (certificate_scale unit2 37)
    · exact certificate_mono (by decide : 76 ≤ 76) (le_refl 38) (certificate_scale unit2 38)
    · exact certificate_mono (by decide : 84 ≤ 84) (le_refl 42) (certificate_scale unit2 42)
    · exact certificate_mono (by decide : 90 ≤ 91) (le_refl 45) (certificate_scale unit2 45)
    · exact certificate_mono (by decide : 92 ≤ 93) (le_refl 46) (certificate_scale unit2 46)
  by_cases h3 : p=3
  · subst p
    change v ∈ ([(54,9),(68,11),(84,14),(91,15),(93,15)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 54 ≤ 54) (le_refl 9) (certificate_scale unit3 9)
    · exact certificate_mono (by decide : 66 ≤ 68) (le_refl 11) (certificate_scale unit3 11)
    · exact certificate_mono (by decide : 84 ≤ 84) (le_refl 14) (certificate_scale unit3 14)
    · exact certificate_mono (by decide : 90 ≤ 91) (le_refl 15) (certificate_scale unit3 15)
    · exact certificate_mono (by decide : 90 ≤ 93) (le_refl 15) (certificate_scale unit3 15)
  by_cases h5 : p=5
  · subst p
    change v ∈ ([(31,2),(33,2),(91,6),(93,6)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact certificate_mono (by decide : 30 ≤ 31) (by decide : 2 ≤ 2) (certificate_scale ClassCertificates155716.cert5_30 1)
    · exact certificate_mono (by decide : 30 ≤ 33) (by decide : 2 ≤ 2) (certificate_scale ClassCertificates155716.cert5_30 1)
    · exact certificate_mono (by decide : 90 ≤ 91) (by decide : 6 ≤ 6) (certificate_scale ClassCertificates155716.cert5_30 3)
    · exact certificate_mono (by decide : 90 ≤ 93) (by decide : 6 ≤ 6) (certificate_scale ClassCertificates155716.cert5_30 3)
  by_cases h7 : p=7
  · subst p
    change v ∈ ([] : List (ℕ × ℕ)) at hv
    contradiction
  by_cases h11 : p=11
  · subst p
    change v ∈ ([(31,4),(33,3),(54,9),(68,12),(84,17),(91,19),(93,18)] : List (ℕ × ℕ)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ClassCycle142758P11N31.cert11_31
    · exact certificate_mono (by decide : 30 ≤ 33) (by decide : 3 ≤ 3) (certificate_add (ClassCertificates150465.class_basis_checked 11 (20,2) (by decide)) (ClassCertificates150465.class_basis_checked 11 (10,1) (by decide)))
    · exact ClassCycle142758P11N54.cert11_54
    · exact ClassCycle142758P11N68.cert11_68
    · exact ClassCycle142758P11N84.cert11_84
    · exact ClassCycle142758P11N91.cert11_91
    · exact certificate_mono (by decide : 91 ≤ 93) (by decide : 18 ≤ 19) ClassCycle142758P11N91.cert11_91
  have he : Extras p=[] := by simp only [Extras, h2, h3, h5, h7, h11, if_false]
  rw [he] at hv
  contradiction

theorem class_basis_checked (p : ℕ) (v : ℕ × ℕ) (hv : v ∈ ClassBasis p) :
    Certificate p v.1 v.2 := by
  rcases List.mem_append.mp hv with h | h
  · exact ClassCertificates150465.class_basis_checked p v h
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
end JSP233.ClassCertificates142758
