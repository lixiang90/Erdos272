import Erdos272.Foundation.StaircaseSupply
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Kernel-checked real analytic tail package for the staircase audit.
The arithmetic Mobius/totient estimates are a separate interface. -/

namespace JSP233.StaircaseTail

noncomputable section

open scoped BigOperators

def tailMajorant (x : ℝ) : ℝ :=
  -(107 / 1000 : ℝ) * x ^ 2 + 3 * x * Real.log x + 10 * x + 6

def tailSlope (x : ℝ) : ℝ :=
  -(214 / 1000 : ℝ) * x + 3 * Real.log x + 13

def tailCurvature (x : ℝ) : ℝ := -(214 / 1000 : ℝ) + 3 / x

theorem small_series_rational : (35303 / 25000 : ℝ) <
    ∑ i ∈ Finset.range 5, (2761 / 8000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem rational_power_gt_250 : (250 : ℝ) < (35303 / 25000 : ℝ) ^ 16 := by
  norm_num

theorem exp_rational_gt_250 : (250 : ℝ) < Real.exp (2761 / 500 : ℝ) := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (2761 / 8000 : ℝ)) (by norm_num) 5
  have hsmall : (35303 / 25000 : ℝ) ≤ Real.exp (2761 / 8000 : ℝ) :=
    (small_series_rational.trans_le hseries).le
  have hpower : (35303 / 25000 : ℝ) ^ 16 ≤ Real.exp (2761 / 8000 : ℝ) ^ 16 := by
    gcongr
  have heq : Real.exp (2761 / 500 : ℝ) = Real.exp (2761 / 8000 : ℝ) ^ 16 := by
    convert Real.exp_nat_mul (2761 / 8000 : ℝ) 16 using 1
    norm_num
  rw [heq]
  exact rational_power_gt_250.trans_le hpower

theorem log_250_lt : Real.log (250 : ℝ) < (2761 / 500 : ℝ) :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 250)).mpr exp_rational_gt_250

theorem log_tangent_250 {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ Real.log (250 : ℝ) + (x - 250) / 250 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 250 by positivity)
  rw [Real.log_div (ne_of_gt hx) (by norm_num : (250 : ℝ) ≠ 0)] at h
  linarith

theorem log_upper_from_250 {x : ℝ} (hx : 0 < x) :
    Real.log x < (2761 / 500 : ℝ) + (x - 250) / 250 := by
  exact (log_tangent_250 hx).trans_lt (by linarith [log_250_lt])

theorem tailMajorant_lt_neg_forty {x : ℝ} (hx : 250 ≤ x) :
    tailMajorant x < -40 := by
  have hpos : 0 < x := by linarith
  have hlog := log_upper_from_250 hpos
  have hscaled := mul_lt_mul_of_pos_left hlog (show 0 < 3 * x by positivity)
  have hsquare : 0 ≤ (x - 250) ^ 2 := sq_nonneg _
  unfold tailMajorant
  nlinarith

theorem tailMajorant_neg {x : ℝ} (hx : 250 ≤ x) : tailMajorant x < 0 :=
  (tailMajorant_lt_neg_forty hx).trans (by norm_num)

theorem hasDerivAt_tailMajorant {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt tailMajorant (tailSlope x) x := by
  have hid := hasDerivAt_id x
  have hlog := Real.hasDerivAt_log hx
  have h := ((((hid.pow 2).const_mul (-(107 / 1000 : ℝ))).add
    ((hid.const_mul 3).mul hlog)).add (hid.const_mul 10)).add_const 6
  apply h.congr_deriv
  dsimp [tailSlope]
  field_simp [hx]
  ring

theorem hasDerivAt_tailSlope {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt tailSlope (tailCurvature x) x := by
  have h := (((hasDerivAt_id x).const_mul (-(214 / 1000 : ℝ))).add
    ((Real.hasDerivAt_log hx).const_mul 3)).add_const 13
  apply h.congr_deriv
  dsimp [tailCurvature]
  ring

theorem tailSlope_neg {x : ℝ} (hx : 250 ≤ x) : tailSlope x < 0 := by
  have hpos : 0 < x := by linarith
  have hlog := log_upper_from_250 hpos
  unfold tailSlope
  linarith

theorem tailCurvature_neg {x : ℝ} (hx : 250 ≤ x) : tailCurvature x < 0 := by
  have hpos : 0 < x := by linarith
  have hinv : 3 / x ≤ (3 / 250 : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold tailCurvature
  linarith

theorem tailMajorant_strictAntiOn : StrictAntiOn tailMajorant (Set.Ici (250 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (250 : ℝ))
  · intro x hx
    exact (hasDerivAt_tailMajorant (by have := hx; simp only [Set.mem_Ici] at this; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 250 ≤ x := Set.mem_Ici.mp (interior_subset hx)
    rw [(hasDerivAt_tailMajorant (by linarith : x ≠ 0)).deriv]
    exact tailSlope_neg hx'

theorem tailSlope_strictAntiOn : StrictAntiOn tailSlope (Set.Ici (250 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (250 : ℝ))
  · intro x hx
    exact (hasDerivAt_tailSlope (by have := hx; simp only [Set.mem_Ici] at this; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 250 ≤ x := Set.mem_Ici.mp (interior_subset hx)
    rw [(hasDerivAt_tailSlope (by linarith : x ≠ 0)).deriv]
    exact tailCurvature_neg hx'

def quadraticLoss (L R : ℝ) : ℝ :=
  (3 / Real.pi ^ 2) * (L ^ 2 + R ^ 2) - (1 - 6 / Real.pi ^ 2) * L * R

def twoVariableMajorant (L R : ℝ) : ℝ :=
  -quadraticLoss L R + L * Real.log R + (3 / 2 : ℝ) * R * Real.log R +
    (1 / 2 : ℝ) * L * Real.log L + 5 * (L + R) + 6

theorem quadraticLoss_lower (L R : ℝ) :
    (107 / 1000 : ℝ) * (max L R) ^ 2 ≤ quadraticLoss L R := by
  have hpi : Real.pi < (22 / 7 : ℝ) := Real.pi_lt_d4.trans (by norm_num)
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hpi2upper : Real.pi ^ 2 < (484 / 49 : ℝ) := by nlinarith [Real.pi_pos]
  have hcoef : (607 / 1000 : ℝ) < 6 / Real.pi ^ 2 :=
    (lt_div_iff₀ hpi2).mpr (by nlinarith)
  have hcoef' : (107 / 1000 : ℝ) ≤ 6 / Real.pi ^ 2 - 1 / 2 := by linarith
  have hodd : 0 ≤ 1 - 6 / Real.pi ^ 2 := by
    have hsq : 6 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hdiv : 6 / Real.pi ^ 2 ≤ (1 : ℝ) := (div_le_one hpi2).mpr hsq
    linarith
  have hproduct := mul_nonneg hodd (sq_nonneg (L - R))
  have hq : (6 / Real.pi ^ 2 - 1 / 2) * (L ^ 2 + R ^ 2) ≤ quadraticLoss L R := by
    apply sub_nonneg.mp
    have heq : quadraticLoss L R - (6 / Real.pi ^ 2 - 1 / 2) * (L ^ 2 + R ^ 2) =
        (1 - 6 / Real.pi ^ 2) * (L - R) ^ 2 / 2 := by
      unfold quadraticLoss
      ring
    rw [heq]
    exact div_nonneg hproduct (by norm_num)
  have hsquares : (max L R) ^ 2 ≤ L ^ 2 + R ^ 2 := by
    rcases le_total L R with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg L]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg R]
  exact (mul_le_mul_of_nonneg_left hsquares (by norm_num)).trans
    ((mul_le_mul_of_nonneg_right hcoef' (by positivity)).trans hq)

theorem twoVariableMajorant_le_tail {L R : ℝ} (hL : 2 ≤ L) (hR : 2 ≤ R) :
    twoVariableMajorant L R ≤ tailMajorant (max L R) := by
  let M := max L R
  have hLM : L ≤ M := le_max_left _ _
  have hRM : R ≤ M := le_max_right _ _
  have hL0 : 0 ≤ L := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hMlog : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlogL : Real.log L ≤ Real.log M := Real.log_le_log (by linarith) hLM
  have hlogR : Real.log R ≤ Real.log M := Real.log_le_log (by linarith) hRM
  have hLR : L * Real.log R ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogR hL0).trans
      (mul_le_mul_of_nonneg_right hLM hMlog)
  have hRR : R * Real.log R ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogR hR0).trans
      (mul_le_mul_of_nonneg_right hRM hMlog)
  have hLL : L * Real.log L ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogL hL0).trans
      (mul_le_mul_of_nonneg_right hLM hMlog)
  have hq := quadraticLoss_lower L R
  change twoVariableMajorant L R ≤ tailMajorant M
  unfold twoVariableMajorant tailMajorant
  change (107 / 1000 : ℝ) * M ^ 2 ≤ quadraticLoss L R at hq
  nlinarith

theorem twoVariableMajorant_lt_neg_forty {L R : ℝ} (hL : 2 ≤ L) (hR : 2 ≤ R)
    (hM : 250 ≤ max L R) : twoVariableMajorant L R < -40 :=
  (twoVariableMajorant_le_tail hL hR).trans_lt (tailMajorant_lt_neg_forty hM)

theorem primitivePhi_eq_totient (n : Nat) :
    StaircaseCertificate.PrimitivePhi n = Nat.totient n := by
  simp only [StaircaseCertificate.PrimitivePhi, Nat.totient, Nat.Coprime, Nat.gcd_comm]

theorem leftSupply_add_two (H : Nat) (hH : 2 ≤ H) :
    StaircaseCertificate.LeftSupply H + 2 =
      ∑ n ∈ Finset.range (H + 1), Nat.totient n := by
  induction H, hH using Nat.le_induction with
  | base => norm_num [StaircaseCertificate.LeftSupply, Finset.sum_range_succ]
  | succ H hH ih =>
    have h3 : 3 ≤ H + 1 := by omega
    have hsupply : StaircaseCertificate.LeftSupply (H + 1) =
        StaircaseCertificate.LeftSupply H + StaircaseCertificate.PrimitivePhi (H + 1) := by
      unfold StaircaseCertificate.LeftSupply
      rw [Finset.sum_range_succ]
      simp only [if_pos h3]
    rw [hsupply, Finset.sum_range_succ, primitivePhi_eq_totient, ← ih]
    omega

theorem primitivePhi_moebius_identity (n : Nat) (hn : 0 < n) :
    (StaircaseCertificate.PrimitivePhi n : ℝ) =
      ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ) * (p.2 : ℝ) := by
  have hsum : ∀ m : Nat, 0 < m → (∑ i ∈ m.divisors, (Nat.totient i : ℝ)) = (m : ℝ) := by
    intro m hm
    exact_mod_cast Nat.sum_totient m
  rw [primitivePhi_eq_totient]
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun m => (Nat.totient m : ℝ)) (g := fun m => (m : ℝ))).mp hsum n hn).symm

#print axioms small_series_rational
#print axioms rational_power_gt_250
#print axioms exp_rational_gt_250
#print axioms log_250_lt
#print axioms log_tangent_250
#print axioms log_upper_from_250
#print axioms tailMajorant_lt_neg_forty
#print axioms tailMajorant_neg
#print axioms hasDerivAt_tailMajorant
#print axioms hasDerivAt_tailSlope
#print axioms tailSlope_neg
#print axioms tailCurvature_neg
#print axioms tailMajorant_strictAntiOn
#print axioms tailSlope_strictAntiOn
#print axioms quadraticLoss_lower
#print axioms twoVariableMajorant_le_tail
#print axioms twoVariableMajorant_lt_neg_forty
#print axioms primitivePhi_eq_totient
#print axioms leftSupply_add_two
#print axioms primitivePhi_moebius_identity

end
end JSP233.StaircaseTail
