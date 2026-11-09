module

public import Erdos272.Resources.CommonPoint208

@[expose] public section
namespace JSP233.CommonCapacity208
open StarCompletion APGeometry NearAP36 FarSlot112
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
theorem actual_common_point_card_le_two {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x : ℤ} (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, APAt d a (core S))
    (ha : ∀ S ∈ F, a ∈ core S)
    (hx : ∀ S ∈ F, x ∈ S \ core S) : F.card ≤ 2 := by
  let lo : Finset ℤ → ℤ := fun S =>
    if h : (core S).Nonempty then (core S).min' h else 0
  let hi : Finset ℤ → ℤ := fun S =>
    if h : (core S).Nonempty then (core S).max' h else 0
  have hlo : ∀ S ∈ F, lo S ∈ core S := by
    intro S hS
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [lo, dif_pos hn] using Finset.min'_mem (core S) hn
  have hhi : ∀ S ∈ F, hi S ∈ core S := by
    intro S hS
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [hi, dif_pos hn] using Finset.max'_mem (core S) hn
  have hbds : ∀ S ∈ F, ∀ y ∈ core S, lo S ≤ y ∧ y ≤ hi S := by
    intro S hS y hy
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [lo, hi, dif_pos hn] using
      And.intro (Finset.min'_le (core S) y hy) (Finset.le_max' (core S) y hy)
  have horder : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → lo S ≤ lo T → hi S ≤ hi T := by
    intro S hS T hT hne hl
    by_contra hr
    have hsub : core T ⊆ core S := by
      intro y hy
      apply ap_mem_of_bounds (hAt S hS) (hlo S hS) (hhi S hS)
      · exact hl.trans (hbds T hT y hy).1
      · exact (hbds T hT y hy).2.trans (le_of_not_ge hr)
      · exact apAt_dvd_sub (hAt T hT) (ha T hT) hy
    exact actual_core_not_subset hF hT hS hne.symm (hcore T hT) (hcore S hS).1
      (Finset.mem_sdiff.mp (hx T hT)).1 (Finset.mem_sdiff.mp (hx S hS)).1
      (Finset.mem_sdiff.mp (hx T hT)).2 hsub
  have hstrict : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → lo S ≤ lo T →
      lo S < lo T ∧ hi S < hi T := by
    intro S hS T hT hST hloST
    have hnotTS := actual_core_not_subset hF hT hS hST.symm (hcore T hT) (hcore S hS).1
      (Finset.mem_sdiff.mp (hx T hT)).1 (Finset.mem_sdiff.mp (hx S hS)).1
      (Finset.mem_sdiff.mp (hx T hT)).2
    have hhiST : hi S < hi T := by
      by_contra hn
      apply hnotTS
      intro y hy
      apply ap_mem_of_bounds (hAt S hS) (hlo S hS) (hhi S hS)
      · exact hloST.trans (hbds T hT y hy).1
      · exact (hbds T hT y hy).2.trans (le_of_not_gt hn)
      · exact apAt_dvd_sub (hAt T hT) (ha T hT) hy
    have hloST' : lo S < lo T := by
      by_contra hn
      have hnotST := actual_core_not_subset hF hS hT hST (hcore S hS) (hcore T hT).1
        (Finset.mem_sdiff.mp (hx S hS)).1 (Finset.mem_sdiff.mp (hx T hT)).1
        (Finset.mem_sdiff.mp (hx S hS)).2
      apply hnotST
      intro y hy
      apply ap_mem_of_bounds (hAt T hT) (hlo T hT) (hhi T hT)
      · exact (le_of_not_gt hn).trans (hbds S hS y hy).1
      · exact (hbds S hS y hy).2.trans hhiST.le
      · exact apAt_dvd_sub (hAt S hS) (ha S hS) hy
    exact ⟨hloST',hhiST⟩
  have hno : ∀ S ∈ F, ∀ T ∈ F, ∀ U ∈ F, S ≠ T → T ≠ U →
      lo S ≤ lo T → lo T ≤ lo U → False := by
    intro S hS T hT U hU hST hTU hSTlo hTUlo
    exact CommonPoint208.no_ordered_three hF hS hT hU hST hTU
      (hcore S hS).1 (hcore T hT) (hcore U hU).1
      (hAt S hS) (hAt T hT) (hAt U hU)
      (ha S hS) (ha T hT) (ha U hU)
      (Finset.mem_sdiff.mp (hx S hS)).1 (Finset.mem_sdiff.mp (hx T hT)).1
      (Finset.mem_sdiff.mp (hx U hU)).1 (Finset.mem_sdiff.mp (hx T hT)).2
      (hlo S hS) (hlo T hT) (hlo U hU) (hhi S hS) (hhi T hT) (hhi U hU)
      (hbds S hS) (hbds T hT) (hbds U hU)
      (hstrict S hS T hT hST hSTlo).1 (hstrict T hT U hU hTU hTUlo).1
      (hstrict S hS T hT hST hSTlo).2 (hstrict T hT U hU hTU hTUlo).2
  by_contra hcard
  obtain ⟨S, T, U, hS, hT, hU, hST, hSU, hTU⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge hcard)
  rcases le_total (lo S) (lo T) with hSTlo | hTSlo
  · rcases le_total (lo T) (lo U) with hTUlo | hUTlo
    · exact hno S hS T hT U hU hST hTU hSTlo hTUlo
    · rcases le_total (lo S) (lo U) with hSUlo | hUSlo
      · exact hno S hS U hU T hT hSU hTU.symm hSUlo hUTlo
      · exact hno U hU S hS T hT hSU.symm hST hUSlo hSTlo
  · rcases le_total (lo S) (lo U) with hSUlo | hUSlo
    · exact hno T hT S hS U hU hST.symm hSU hTSlo hSUlo
    · rcases le_total (lo T) (lo U) with hTUlo | hUTlo
      · exact hno T hT U hU S hS hTU hSU.symm hTUlo hUSlo
      · exact hno U hU T hT S hS hTU.symm hST.symm hUTlo hTSlo


#print axioms actual_common_point_card_le_two
end
end JSP233.CommonCapacity208
