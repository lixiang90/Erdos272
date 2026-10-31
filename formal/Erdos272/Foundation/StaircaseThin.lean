import Erdos272.Foundation.StaircaseSupply

/-! Actual thin-side unit-interval families inject into their primitive bad-pair pool.
No profile cap, analytic estimate, or StarBound hypothesis is used. -/

namespace JSP233.StaircaseThin

open StarCompletion StaircaseGeometry StaircaseSupply StaircaseCertificate

def leftThinPair (p : Nat × Nat) : Finset Int :=
  {if p.1 = 0 then 1 else -1, (p.2 : Int)}

def rightThinPair (p : Nat × Nat) : Finset Int :=
  {-(p.1 : Int), if p.2 = 0 then -1 else 1}

theorem leftThinPair_injective {p q : Nat × Nat}
    (hp : p.1 ≤ 1) (hq : q.1 ≤ 1) (hpr : 2 ≤ p.2) (hqr : 2 ≤ q.2)
    (heq : leftThinPair p = leftThinPair q) : p = q := by
  have hpl : (if p.1 = 0 then 1 else -1 : Int) < (p.2 : Int) := by
    split_ifs <;> omega
  have hql : (if q.1 = 0 then 1 else -1 : Int) < (q.2 : Int) := by
    split_ifs <;> omega
  have he := ordered_pair_ext hpl hql heq
  apply Prod.ext
  · by_cases hp0 : p.1 = 0 <;> by_cases hq0 : q.1 = 0 <;>
      simp only [hp0, hq0, if_true, if_false] at he <;> omega
  · omega

theorem rightThinPair_injective {p q : Nat × Nat}
    (hp : p.2 ≤ 1) (hq : q.2 ≤ 1) (hpl : 2 ≤ p.1) (hql : 2 ≤ q.1)
    (heq : rightThinPair p = rightThinPair q) : p = q := by
  have hpr : -(p.1 : Int) < (if p.2 = 0 then -1 else 1 : Int) := by
    split_ifs <;> omega
  have hqr : -(q.1 : Int) < (if q.2 = 0 then -1 else 1 : Int) := by
    split_ifs <;> omega
  have he := ordered_pair_ext hpr hqr heq
  apply Prod.ext
  · omega
  · by_cases hp0 : p.2 = 0 <;> by_cases hq0 : q.2 = 0 <;>
      simp only [hp0, hq0, if_true, if_false] at he <;> omega

theorem leftThinPair_primitive {p : Nat × Nat} (hv : Valid p) (hl : p.1 ≤ 1) :
    IsPrimitiveBadPair (leftThinPair p) := by
  have hlen : 3 ≤ p.1 + p.2 := hv
  by_cases hzero : p.1 = 0
  · have hr : 3 ≤ p.2 := by omega
    simpa [leftThinPair, hzero] using
      (positive_pair_iff p.2 1 (by omega) (by omega)).mpr ⟨by simp, hr⟩
  · have hl1 : p.1 = 1 := by omega
    have hr : 2 ≤ p.2 := by omega
    simpa [leftThinPair, hzero] using
      (mixed_pair_iff 1 p.2 (by omega) (by omega)).mpr ⟨by simp, by omega⟩

theorem rightThinPair_primitive {p : Nat × Nat} (hv : Valid p) (hr : p.2 ≤ 1) :
    IsPrimitiveBadPair (rightThinPair p) := by
  have hlen : 3 ≤ p.1 + p.2 := hv
  by_cases hzero : p.2 = 0
  · have hl : 3 ≤ p.1 := by omega
    simpa [rightThinPair, hzero] using
      (negative_pair_iff p.1 1 (by omega) (by omega)).mpr ⟨by simp, hl⟩
  · have hr1 : p.2 = 1 := by omega
    have hl : 2 ≤ p.1 := by omega
    simpa [rightThinPair, hzero] using
      (mixed_pair_iff p.1 1 (by omega) (by omega)).mpr ⟨by simp, by omega⟩

theorem leftThinPair_subset {p : Nat × Nat} (hv : Valid p) (hl : p.1 ≤ 1) :
    leftThinPair p ⊆ Window p.1 p.2 := by
  have hlen : 3 ≤ p.1 + p.2 := hv
  intro x hx
  simp only [leftThinPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_window]
  split_ifs at hx <;> omega

theorem rightThinPair_subset {p : Nat × Nat} (hv : Valid p) (hr : p.2 ≤ 1) :
    rightThinPair p ⊆ Window p.1 p.2 := by
  have hlen : 3 ≤ p.1 + p.2 := hv
  intro x hx
  simp only [rightThinPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_window]
  split_ifs at hx <;> omega

theorem leftThinPair_mem_pool {C : Finset (Nat × Nat)} {p : Nat × Nat}
    (hp : p ∈ C) (hv : Valid p) (hl : p.1 ≤ 1) :
    leftThinPair p ∈ PrimitivePool (Family C) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨Window p.1 p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
  exact (mem_primitiveBadPairs _ _).mpr ⟨leftThinPair_subset hv hl, leftThinPair_primitive hv hl⟩

theorem rightThinPair_mem_pool {C : Finset (Nat × Nat)} {p : Nat × Nat}
    (hp : p ∈ C) (hv : Valid p) (hr : p.2 ≤ 1) :
    rightThinPair p ∈ PrimitivePool (Family C) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨Window p.1 p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
  exact (mem_primitiveBadPairs _ _).mpr ⟨rightThinPair_subset hv hr, rightThinPair_primitive hv hr⟩

theorem left_thin_coordinates_card {C : Finset (Nat × Nat)}
    (hv : ∀ p ∈ C, Valid p) (hl : ∀ p ∈ C, p.1 ≤ 1) :
    (Family C).card ≤ (PrimitivePool (Family C)).card := by
  have hinj : Set.InjOn leftThinPair (C : Set (Nat × Nat)) := by
    intro p hp q hq heq
    have hpv : 3 ≤ p.1 + p.2 := hv p hp
    have hqv : 3 ≤ q.1 + q.2 := hv q hq
    exact leftThinPair_injective (hl p hp) (hl q hq) (by have := hl p hp; omega)
      (by have := hl q hq; omega) heq
  have hcard : (C.image leftThinPair).card = C.card := Finset.card_image_of_injOn hinj
  rw [family_card, ← hcard]
  apply Finset.card_le_card
  intro pair hpair
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpair
  exact leftThinPair_mem_pool hp (hv p hp) (hl p hp)

theorem right_thin_coordinates_card {C : Finset (Nat × Nat)}
    (hv : ∀ p ∈ C, Valid p) (hr : ∀ p ∈ C, p.2 ≤ 1) :
    (Family C).card ≤ (PrimitivePool (Family C)).card := by
  have hinj : Set.InjOn rightThinPair (C : Set (Nat × Nat)) := by
    intro p hp q hq heq
    have hpv : 3 ≤ p.1 + p.2 := hv p hp
    have hqv : 3 ≤ q.1 + q.2 := hv q hq
    exact rightThinPair_injective (hr p hp) (hr q hq) (by have := hr p hp; omega)
      (by have := hr q hq; omega) heq
  have hcard : (C.image rightThinPair).card = C.card := Finset.card_image_of_injOn hinj
  rw [family_card, ← hcard]
  apply Finset.card_le_card
  intro pair hpair
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpair
  exact rightThinPair_mem_pool hp (hv p hp) (hr p hp)

theorem actual_left_thin_family_card (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card ∧ l ≤ 1) :
    F.card ≤ (PrimitivePool F).card := by
  obtain ⟨C, hC, hvalid⟩ := exists_coordinates F (by
    intro S hS
    obtain ⟨l, r, heq, hlarge, hl⟩ := hF S hS
    exact ⟨l, r, heq, hlarge⟩)
  have hthin : ∀ p ∈ C, p.1 ≤ 1 := by
    intro p hp
    have hS : Window p.1 p.2 ∈ F := by
      rw [← hC]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨l, r, heq, hlarge, hl⟩ := hF _ hS
    have hcoords : p = (l, r) := window_injective heq
    simpa only [hcoords] using hl
  rw [← hC]
  exact left_thin_coordinates_card hvalid hthin

theorem actual_right_thin_family_card (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card ∧ r ≤ 1) :
    F.card ≤ (PrimitivePool F).card := by
  obtain ⟨C, hC, hvalid⟩ := exists_coordinates F (by
    intro S hS
    obtain ⟨l, r, heq, hlarge, hr⟩ := hF S hS
    exact ⟨l, r, heq, hlarge⟩)
  have hthin : ∀ p ∈ C, p.2 ≤ 1 := by
    intro p hp
    have hS : Window p.1 p.2 ∈ F := by
      rw [← hC]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨l, r, heq, hlarge, hr⟩ := hF _ hS
    have hcoords : p = (l, r) := window_injective heq
    simpa only [hcoords] using hr
  rw [← hC]
  exact right_thin_coordinates_card hvalid hthin

theorem actual_left_thin_defect_nonpos (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card ∧ l ≤ 1) :
    (F.card : Int) - (PrimitivePool F).card ≤ 0 := by
  exact sub_nonpos.mpr (Int.ofNat_le.mpr (actual_left_thin_family_card F hF))

theorem actual_right_thin_defect_nonpos (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card ∧ r ≤ 1) :
    (F.card : Int) - (PrimitivePool F).card ≤ 0 := by
  exact sub_nonpos.mpr (Int.ofNat_le.mpr (actual_right_thin_family_card F hF))

#print axioms leftThinPair_injective
#print axioms rightThinPair_injective
#print axioms leftThinPair_primitive
#print axioms rightThinPair_primitive
#print axioms leftThinPair_subset
#print axioms rightThinPair_subset
#print axioms leftThinPair_mem_pool
#print axioms rightThinPair_mem_pool
#print axioms left_thin_coordinates_card
#print axioms right_thin_coordinates_card
#print axioms actual_left_thin_family_card
#print axioms actual_right_thin_family_card
#print axioms actual_left_thin_defect_nonpos
#print axioms actual_right_thin_defect_nonpos

end JSP233.StaircaseThin
