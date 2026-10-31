import Erdos272.Foundation.StarCompletion
import Mathlib.Tactic

/-! Algebraic coupling for the whole-family root branch of the 400m proof.
The estimates on the actual root part and all avoiders remain explicit inputs.
This module does not claim the missing Far bound or original-family restoration.
-/
namespace JSP233.RootEnvelope112
open StarCompletion

theorem min_linear_reciprocal_bound {A B β x : ℝ}
    (hβ : 0 < β) (hB : 0 ≤ B) (hx : 1 ≤ x) :
    min β (A*x) + B/x ≤ max (A+B) (β+A*B/β) := by
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx
  by_cases hAx : β ≤ A*x
  · rw [min_eq_left hAx]
    have hb : B/x ≤ A*B/β := by
      apply (div_le_div_iff₀ hxp hβ).mpr
      nlinarith [mul_le_mul_of_nonneg_left hAx hB]
    exact (by linarith : β+B/x ≤ β+A*B/β).trans (le_max_right _ _)
  · have hAx' : A*x ≤ β := le_of_lt (lt_of_not_ge hAx)
    rw [min_eq_right hAx']
    by_cases hBβ : B ≤ β
    · have hbx : 0 ≤ β*x-B := by nlinarith
      have he : (β+A*B/β-(A*x+B/x))*(β*x) =
          (β-A*x)*(β*x-B) := by
        field_simp [hβ.ne',hxp.ne']
        ring
      have hd : 0 ≤ β+A*B/β-(A*x+B/x) := by
        apply (mul_nonneg_iff_of_pos_right (mul_pos hβ hxp)).mp
        rw [he]
        exact mul_nonneg (sub_nonneg.mpr hAx') hbx
      exact (by linarith : A*x+B/x ≤ β+A*B/β).trans (le_max_right _ _)
    · have hbx : 0 ≤ B-A*x := by linarith
      have he : (A+B-(A*x+B/x))*x = (x-1)*(B-A*x) := by
        field_simp [hxp.ne']
        ring
      have hd : 0 ≤ A+B-(A*x+B/x) := by
        apply (mul_nonneg_iff_of_pos_right hxp).mp
        rw [he]
        exact mul_nonneg (sub_nonneg.mpr hx) hbx
      exact (by linarith : A*x+B/x ≤ A+B).trans (le_max_left _ _)

theorem cubic_tail_le_reciprocal {ν g x : ℝ}
    (hg : 0 ≤ g) (hx : 1 ≤ x) :
    ν/x + g/x^3 ≤ (ν+g)/x := by
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx
  have hp : 0 ≤ x*(x-1)*(x+1) :=
    mul_nonneg (mul_nonneg hxp.le (sub_nonneg.mpr hx)) (by linarith)
  have hx3 : x ≤ x^3 := by nlinarith
  have hb : g/x^3 ≤ g/x := by
    apply (div_le_div_iff₀ (pow_pos hxp 3) hxp).mpr
    exact mul_le_mul_of_nonneg_left hx3 hg
  rw [add_div]
  linarith

theorem whole_root_envelope {A ν g β x η : ℝ}
    (hβ : 0 < β) (hν : 0 ≤ ν) (hg : 0 ≤ g) (hx : 1 ≤ x) :
    min β (A*x) + ν/x + g/x^3 + η ≤
      max (A+(ν+g)) (β+A*(ν+g)/β) + η := by
  have ht := cubic_tail_le_reciprocal (ν:=ν) hg hx
  have he := min_linear_reciprocal_bound (A:=A) hβ (add_nonneg hν hg) hx
  linarith

theorem root_partition_bound_of_estimates
    {F : Finset (Finset ℤ)} {c : ℤ} {N : ℕ} {A ν g β x η : ℝ}
    (hβ : 0 < β) (hν : 0 ≤ ν) (hg : 0 ≤ g) (hx : 1 ≤ x)
    (hroot : ((RootPart F c).card:ℝ)/(N:ℝ)^2 ≤ min β (A*x))
    (havoid : ((Avoiders F c).card:ℝ)/(N:ℝ)^2 ≤ ν/x+g/x^3+η) :
    (F.card:ℝ)/(N:ℝ)^2 ≤ max (A+(ν+g)) (β+A*(ν+g)/β)+η := by
  have hp : ((RootPart F c).card:ℝ)/(N:ℝ)^2+
      ((Avoiders F c).card:ℝ)/(N:ℝ)^2 = (F.card:ℝ)/(N:ℝ)^2 := by
    rw [←add_div,←Nat.cast_add,root_avoider_card_partition]
  have he := whole_root_envelope (A:=A) (η:=η) hβ hν hg hx
  linarith

#print axioms min_linear_reciprocal_bound
#print axioms cubic_tail_le_reciprocal
#print axioms whole_root_envelope
#print axioms root_partition_bound_of_estimates
end JSP233.RootEnvelope112
