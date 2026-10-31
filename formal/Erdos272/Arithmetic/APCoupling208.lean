import Mathlib.Tactic

/-! The exact common response of the longest actual AP and the one residual
triple pool used in round207.  This file proves the universal real inequality;
the counting hypotheses in `joint_payment` must still be supplied for the
same family and the same AP. -/
namespace JSP233.APCoupling208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def T : ℝ := 107 / 1250
def Kappa : ℝ := 13 / 50
def APCoefficient (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then a^2 / 2 else 1 / 4 - (1 - a)^2 / 2

def Gap (a t : ℝ) : ℝ := (1 - a)^2 / 2 - t * (1 - Kappa - a^3)

theorem endpoint_sos (a : ℝ) :
    Gap a T = T * a * (a - 33 / 40)^2 +
      (16031 / 25000 : ℝ) * (a - 2116523 / 2564960)^2 +
      351085511 / 10259840000000 := by
  norm_num [Gap, T, Kappa]
  ring

theorem endpoint_gap_pos {a : ℝ} (ha : 0 ≤ a) : 0 < Gap a T := by
  rw [endpoint_sos]
  have hc := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ T by norm_num [T]) ha)
    (sq_nonneg (a - 33 / 40))
  have hq := mul_nonneg (show (0 : ℝ) ≤ 16031 / 25000 by norm_num)
    (sq_nonneg (a - 2116523 / 2564960))
  linarith only [hc, hq]

theorem gap_interpolation (a t : ℝ) :
    T * Gap a t = t * Gap a T + (T - t) * Gap a 0 := by
  unfold Gap
  ring

theorem gap_nonneg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hT : t ≤ T) :
    0 ≤ Gap a t := by
  have hp := (endpoint_gap_pos ha).le
  have hz : 0 ≤ Gap a 0 := by simp only [Gap, zero_mul, sub_zero]; positivity
  have hsum := add_nonneg (mul_nonneg ht hp) (mul_nonneg (sub_nonneg.mpr hT) hz)
  rw [← gap_interpolation] at hsum
  exact nonneg_of_mul_nonneg_right hsum (by norm_num [T])

theorem common_response {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hT : t ≤ T) :
    APCoefficient a + t * (1 - a^3) ≤ 1 / 4 + Kappa * t := by
  unfold APCoefficient
  split_ifs with hhalf
  · have hsq : a^2 ≤ (1 / 4 : ℝ) := by
      have hh := mul_nonneg (sub_nonneg.mpr hhalf)
        (show (0 : ℝ) ≤ 1 / 2 + a by linarith only [ha])
      nlinarith only [hh]
    have hc := mul_nonneg ht (pow_nonneg ha 3)
    norm_num [T, Kappa] at hT ⊢
    nlinarith only [hsq, hc, hT]
  · have hg := gap_nonneg ha ht hT
    dsimp only [Gap] at hg
    linarith only [hg]

/- The two premise bounds refer to one fixed `a`, rather than independently
maximizing the AP count and the residual source count. -/
theorem joint_payment {a t ap other apError otherError : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hT : t ≤ T)
    (hAP : ap ≤ APCoefficient a + apError)
    (hother : other ≤ t * (1 - a^3) + otherError) :
    ap + other ≤ 1 / 4 + Kappa * t + apError + otherError := by
  have hp := common_response ha ht hT
  linarith only [hAP, hother, hp]

theorem actual207_source_range {n : ℕ} (hn : n ≤ 705097) :
    0 ≤ (n : ℝ) / 8681676 ∧ (n : ℝ) / 8681676 ≤ T ∧
    0 ≤ (n : ℝ) / 8809656 ∧ (n : ℝ) / 8809656 ≤ T := by
  have hnR : (n : ℝ) ≤ 705097 := by exact_mod_cast hn
  norm_num [T]
  constructor
  · positivity
  constructor
  · linarith only [hnR]
  constructor
  · positivity
  · linarith only [hnR]

#print axioms common_response
#print axioms joint_payment
#print axioms actual207_source_range
end
end JSP233.APCoupling208
