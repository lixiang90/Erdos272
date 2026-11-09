module

public import Erdos272.Arithmetic.N291012.IntervalShadowFrame291012
public import Erdos272.Counting.UnitCount218
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.UnitShadowGeometry291012
open StarCompletion APGeometry APCount41 UnitCount218
open APShadowCapacity16858 IntervalFamilyEndpoints16858 IntervalShadowFrame291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem interval_geometry {N : ℕ} {c : ℤ} {U : Finset (Finset ℤ)}
    (hc : c ∈ Ground N) (hground : ∀ S ∈ U, S ⊆ Ground N)
    (hroot : ∀ S ∈ U, c ∈ S) (hi : ∀ S ∈ U, ∃ a b : ℤ, S = Finset.Icc a b)
    (htwo : ∀ S ∈ U, 2 ≤ S.card) :
    ∃ y : ℝ, 0 ≤ y ∧ y^2 ≤ ((N-1 : ℕ) : ℝ)^2/4 ∧
      (U.card : ℝ) ≤ y^2+(N-1 : ℕ) ∧
      8*y^3 ≤ 6*((APShadow U).card : ℝ)+(N-1 : ℕ) := by
  obtain ⟨A, B, hsum, hD, hcount, hshadow⟩ := actual_frame hc hground hroot hi htwo
  let D := Pairs c A B U
  let y := Real.sqrt (D.card : ℝ)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hyK : y^2 = (D.card : ℝ) := Real.sq_sqrt (by positivity)
  have harea : (D.card : ℝ) ≤ (A : ℝ)*B := by
    have hprod : ((Finset.range A).product (Finset.range B)).card = A*B := by
      simp
    have hh := (Finset.card_le_card hD).trans_eq hprod
    exact_mod_cast hh
  have hsumR : (A : ℝ)+B ≤ (N-1 : ℕ) := by exact_mod_cast hsum
  have hsquare := mul_nonneg (sub_nonneg.mpr hsumR)
    (show 0 ≤ ((N-1 : ℕ) : ℝ)+(A+B) by positivity)
  have hAB := sq_nonneg ((A : ℝ)-B)
  have hybound : y^2 ≤ ((N-1 : ℕ) : ℝ)^2/4 := by
    nlinarith only [hyK, harea, hsquare, hAB]
  let X : ℝ := ∑ p ∈ D, (2*(p.1 : ℝ)+1)
  let Y : ℝ := ∑ p ∈ D, (2*(p.2 : ℝ)+1)
  let h : ℝ := ((A : ℝ)^3+(B : ℝ)^3-A-B+3*(X+Y))/6
  have hformula : 6*h = (A : ℝ)^3+(B : ℝ)^3-A-B+3*(X+Y) := by dsimp only [h]; ring
  have hmass := UnitShadowGrid218.actual_discrete_shadow_mass hD hy hyK hformula
  have hmoment : X+Y = 2*(∑ p ∈ D, ((p.1 : ℝ)+p.2+1)) := by
    dsimp only [X, Y]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hsmall : 6*h ≤ 6*((APShadow U).card : ℝ) := by
    change (A : ℝ)^3+(B : ℝ)^3-A-B+
      6*(∑ p ∈ D, ((p.1 : ℝ)+p.2+1)) ≤ _ at hshadow
    nlinarith only [hshadow, hformula, hmoment]
  refine ⟨y, hy, hybound, ?_, ?_⟩
  · nlinarith only [hcount, hyK, hsumR]
  · linarith only [hmass, hsmall, hsumR]

theorem actual_unit_geometry {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) :
    ∃ y : ℝ, 0 ≤ y ∧ y^2 ≤ ((N-1 : ℕ) : ℝ)^2/4 ∧
      ((UnitAP F).card : ℝ) ≤ y^2+(N-1 : ℕ) ∧
      8*y^3 ≤ 6*((APShadow (UnitAP F)).card : ℝ)+(N-1 : ℕ) := by
  have hsub : UnitAP F ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (UnitAP F) :=
    ⟨fun S hS => hF.1 S (hsub hS),
      fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
  have htwo : ∀ S ∈ UnitAP F, 2 ≤ S.card :=
    fun S hS => (Finset.mem_filter.mp hS).2.2.1
  have hstep : ∀ S ∈ UnitAP F, ∃ p : ℤ, APAt (1 : ℤ) p S := by
    intro S hS
    obtain ⟨hSF, hAP, _htwo, hs⟩ := Finset.mem_filter.mp hS
    obtain ⟨_hd, p, hp⟩ := actual_step hAP
    exact ⟨p, by simpa only [hs, Nat.cast_one] using hp⟩
  by_cases hne : (UnitAP F).Nonempty
  · have hnonempty : ∀ S ∈ UnitAP F, S.Nonempty := by
      intro S hS
      exact Finset.card_pos.mp (by have hh := htwo S hS; omega)
    obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root (d := 1) hne hlegal hnonempty hstep
    exact interval_geometry hc hlegal.1 hroot
      (fun S hS => by obtain ⟨p, hp⟩ := hstep S hS; exact NonIntervalAP47.actual_step_one_interval hp)
      htwo
  · have he : UnitAP F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, le_rfl, ?_, ?_, ?_⟩
    · calc
        (0 : ℝ)^2 = 0 := by norm_num
        _ ≤ ((N-1 : ℕ) : ℝ)^2/4 := by positivity
    · simp [he]
    · simp [he, APShadow]

#print axioms interval_geometry
#print axioms actual_unit_geometry
end
end JSP233.UnitShadowGeometry291012
