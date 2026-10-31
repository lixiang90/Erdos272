import Erdos272.Resources.IntrinsicTriples208
import Erdos272.Arithmetic.APCoupling208

/-! The reserved triples of one actual AP member and the actual intrinsic
triple supply are connected to the universal common-response inequality. -/
namespace JSP233.APResidual208
open StarCompletion IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem cast_choose_three (n : ℕ) :
    (n.choose 3 : ℝ) = (n : ℝ) * (n - 1) * (n - 2) / 6 := by
  by_cases hn : 2 ≤ n
  · have hh := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq n 2)
    simp only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_choose_two] at hh
    nlinarith only [hh]
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> norm_num [Nat.choose_eq_zero_of_lt]

theorem choose_difference_cubic {n a : ℕ} (ha : a ≤ n) :
    (n.choose 3 : ℝ) - (a.choose 3 : ℝ) ≤ ((n : ℝ)^3 - (a : ℝ)^3) / 6 := by
  by_cases hn : n = 0
  · have ha0 : a = 0 := by omega
    simp only [hn, ha0, sub_self, zero_div, le_refl]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have haR : (a : ℝ) ≤ n := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hp := mul_nonneg (sub_nonneg.mpr haR)
    (show 0 ≤ 3 * ((n : ℝ) + a) - 2 by linarith only [hnR, ha0])
  rw [cast_choose_three, cast_choose_three]
  nlinarith only [hp]

theorem actual_residual_cubic {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (hF : Legal Ω F) (hP : P ∈ F) (hAP : IsAP P) :
    (∑ S ∈ F, ((Pool S).card : ℝ)) ≤ ((Ω.card : ℝ)^3 - (P.card : ℝ)^3) / 6 := by
  have hcap := actual_capacity_with_AP hF hP hAP
  have hcapR : (∑ S ∈ F, ((Pool S).card : ℝ)) + (P.card.choose 3 : ℝ) ≤
      (Ω.card.choose 3 : ℝ) := by exact_mod_cast hcap
  have ha : P.card ≤ Ω.card := Finset.card_le_card (hF.1 P hP)
  have hc := choose_difference_cubic ha
  linarith only [hcapR, hc]

/-- The lower source demand and the AP count must use this same actual P.
The finite source tables will eventually discharge `hsource`; this theorem
does not infer any table entry from an external computation. -/
theorem actual_joint_payment {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    {t ap crooked apError otherError : ℝ}
    (hN : 0 < Ω.card) (hF : Legal Ω F) (hP : P ∈ F) (hAP : IsAP P)
    (ht : 0 ≤ t) (hT : t ≤ APCoupling208.T)
    (hAPcount : ap ≤ APCoupling208.APCoefficient ((P.card : ℝ) / Ω.card) + apError)
    (hsource : crooked ≤ 6 * t / (Ω.card : ℝ)^3 *
      (∑ S ∈ F, ((Pool S).card : ℝ)) + otherError) :
    ap + crooked ≤ 1 / 4 + APCoupling208.Kappa * t + apError + otherError := by
  have hNp : (0 : ℝ) < Ω.card := by exact_mod_cast hN
  have hcapacity := actual_residual_cubic hF hP hAP
  have hfee := mul_le_mul_of_nonneg_left hcapacity
    (show 0 ≤ 6 * t / (Ω.card : ℝ)^3 by positivity)
  have he : 6 * t / (Ω.card : ℝ)^3 * (((Ω.card : ℝ)^3 - (P.card : ℝ)^3) / 6) =
      t * (1 - ((P.card : ℝ) / Ω.card)^3) := by
    field_simp [hNp.ne']
  rw [he] at hfee
  apply APCoupling208.joint_payment (by positivity) ht hT hAPcount
  linarith only [hsource, hfee]

#print axioms actual_residual_cubic
#print axioms actual_joint_payment
end
end JSP233.APResidual208
