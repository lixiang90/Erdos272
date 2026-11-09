module

public import Erdos272.Counting.APCount41
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual unit-step APs with a common root, separated by their actual lengths. -/
namespace JSP233.APLength208
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_unit_span {S : Finset ℤ} {p : ℤ} (hne : S.Nonempty)
    (hp : APAt 1 p S) : High S - Low S = (S.card : ℤ) - 1 := by
  simpa only [High, Low, dif_pos hne, one_mul] using apAt_span_eq hp hne

theorem actual_fixed_length_low_injective {F : Finset (Finset ℤ)} {ell : ℕ}
    (hne : ∀ S ∈ F, S.Nonempty) (hlen : ∀ S ∈ F, S.card = ell)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APAt 1 p S) : Set.InjOn Low F := by
  intro S hS T hT he
  obtain ⟨p, hp⟩ := hstep S hS
  obtain ⟨q, hq⟩ := hstep T hT
  have hs := actual_unit_span (hne S hS) hp
  have ht := actual_unit_span (hne T hT) hq
  rw [hlen S hS] at hs
  rw [hlen T hT] at ht
  apply same_step_equal_of_endpoints (d := 1) (hne S hS) (hne T hT) hp hq he
  omega

theorem actual_fixed_length_count {N ell : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hell : 1 ≤ ell) (hsub : ∀ S ∈ F, S ⊆ Ground N)
    (hroot : ∀ S ∈ F, c ∈ S) (hlen : ∀ S ∈ F, S.card = ell)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APAt 1 p S) :
    F.card ≤ min ell (N - ell + 1) := by
  have hne : ∀ S ∈ F, S.Nonempty := fun S hS => ⟨c, hroot S hS⟩
  have hspan : ∀ S ∈ F, High S - Low S = (ell : ℤ) - 1 := by
    intro S hS
    obtain ⟨p, hp⟩ := hstep S hS
    simpa only [hlen S hS] using actual_unit_span (hne S hS) hp
  have hi := actual_fixed_length_low_injective hne hlen hstep
  apply le_min
  · have hm : Set.MapsTo Low F (Finset.Icc (c - ell + 1) c) := by
      intro S hS
      have hlo := (low_spec (hne S hS)).2 c (hroot S hS)
      have hhi := (high_spec (hne S hS)).2 c (hroot S hS)
      have hs := hspan S hS
      apply Finset.mem_Icc.mpr
      omega
    have hb := Finset.card_le_card_of_injOn Low hm hi
    have hc : (Finset.Icc (c - ell + 1) c).card = ell := by
      rw [Int.card_Icc]
      omega
    simpa only [hc] using hb
  · have hm : Set.MapsTo Low F (Finset.Icc (1 : ℤ) ((N : ℤ) - ell + 1)) := by
      intro S hS
      have hlo := (mem_ground N (Low S)).mp (hsub S hS (low_spec (hne S hS)).1)
      have hhi := (mem_ground N (High S)).mp (hsub S hS (high_spec (hne S hS)).1)
      have hs := hspan S hS
      apply Finset.mem_Icc.mpr
      omega
    have hb := Finset.card_le_card_of_injOn Low hm hi
    have hc : (Finset.Icc (1 : ℤ) ((N : ℤ) - ell + 1)).card ≤ N - ell + 1 := by
      rw [Int.card_Icc]
      omega
    exact hb.trans hc

def LengthCount (N a : ℕ) : ℕ := ∑ ell ∈ Finset.Icc 2 a, min ell (N - ell + 1)

theorem actual_unit_step_length_count {N a : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hne : ∀ S ∈ F, S.Nonempty)
    (hlen : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ a)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APAt 1 p S) : F.card ≤ LengthCount N a := by
  by_cases hF : F.Nonempty
  · obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root (d := 1) hF hlegal hne hstep
    have hmaps : ∀ S ∈ F, S.card ∈ Finset.Icc 2 a := by
      intro S hS
      exact Finset.mem_Icc.mpr (hlen S hS)
    have he := Finset.card_eq_sum_card_fiberwise hmaps
    rw [he]
    apply Finset.sum_le_sum
    intro ell hell
    apply actual_fixed_length_count (c := c) (by have hh := (Finset.mem_Icc.mp hell).1; omega)
      (fun S hS => hlegal.1 S (Finset.mem_filter.mp hS).1)
      (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
      (fun S hS => hstep S (Finset.mem_filter.mp hS).1)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [he, Finset.card_empty]
    exact Nat.zero_le _

#print axioms actual_fixed_length_count
#print axioms actual_unit_step_length_count
end
end JSP233.APLength208
