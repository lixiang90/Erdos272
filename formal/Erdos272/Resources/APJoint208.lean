module

public import Erdos272.Counting.APTail208
public import Erdos272.Resources.APResidual208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The AP and triple terms are paid for the same original family and the
same longest actual AP member. Only the near/source fee remains an input. -/
namespace JSP233.APJoint208
open StarCompletion APResidual208 IntrinsicTriples208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_original_joint_payment {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    {g fee : ℝ} (hN : 1 ≤ N) (hF : Legal (Ground N) F)
    (hP : P ∈ F) (hAP : IsAP P) (hmax : ∀ S ∈ F, IsAP S → S.card ≤ P.card)
    (hg : 0 ≤ g) (hT : g * N ≤ APCoupling208.T)
    (hsource : ((F.filter fun S => ¬ IsAP S).card : ℝ) ≤
      6 * g * (∑ S ∈ F, ((Pool S).card : ℝ)) + fee) :
    (F.card : ℝ) ≤ (329 / 800 : ℝ) * N^2 + APCoupling208.Kappa * g * N^3 +
      (N : ℝ) * Harmonic N + 1 + fee := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount := APTail208.actual_AP_members_profile hN hF hP hAP hmax
  have hres := actual_residual_cubic hF hP hAP
  simp only [ground_card] at hres
  have hmass := mul_le_mul_of_nonneg_left hres (show 0 ≤ 6 * g by positivity)
  have hnonAP : ((F.filter fun S => ¬ IsAP S).card : ℝ) ≤
      g * ((N : ℝ)^3 - (P.card : ℝ)^3) + fee := by
    nlinarith only [hsource, hmass]
  have hjoint := mul_le_mul_of_nonneg_left
    (APCoupling208.common_response (by positivity : 0 ≤ (P.card : ℝ) / N)
      (show 0 ≤ g * N by positivity) hT) (sq_nonneg (N : ℝ))
  have he : (N : ℝ)^2 * (((P.card : ℝ) / N)^3 * (g * N)) = g * (P.card : ℝ)^3 := by
    field_simp
  have hbudget :
      (N : ℝ)^2 * APCoupling208.APCoefficient ((P.card : ℝ) / N) +
        g * ((N : ℝ)^3 - (P.card : ℝ)^3) ≤
      (N : ℝ)^2 / 4 + APCoupling208.Kappa * g * N^3 := by
    nlinarith only [hjoint, he]
  have hp := Finset.card_filter_add_card_filter_not (s := F) IsAP
  have hpR : ((F.filter IsAP).card : ℝ) + ((F.filter fun S => ¬ IsAP S).card : ℝ) = F.card := by
    exact_mod_cast hp
  nlinarith only [hcount, hnonAP, hbudget, hpR]

#print axioms actual_original_joint_payment
end
end JSP233.APJoint208
