module

public import Erdos272.Arithmetic.N20258.RootWidth20258
public import Erdos272.Arithmetic.HarmonicSharp39
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
namespace JSP233.DyadicWidth20258
open HarmonicAbel29
noncomputable section
set_option autoImplicit false

def coefficient (L : ℕ) : ℝ :=
  102/25+2*Harmonic L+(Real.log L)^2/4+(7/10)*Real.log L+3/5

private theorem coeff_le {L j : ℕ} (pos : 1 ≤ L) (hi : L < 2^j) :
    coefficient L ≤ 102/25+2*(53/100+(7/10)*(j : ℝ))+
      ((7/10)*(j : ℝ))^2/4+(7/10)*((7/10)*(j : ℝ))+3/5 := by
  have one : (1 : ℝ) ≤ L := by exact_mod_cast pos
  have power : (L : ℝ) ≤ (2 : ℝ)^j := by exact_mod_cast hi.le
  have hlog := Real.log_le_log (by linarith only [one] : (0 : ℝ) < L) power
  rw [Real.log_pow] at hlog
  have two : Real.log 2 ≤ 7/10 := Real.log_two_lt_d9.le.trans (by norm_num)
  have upper : Real.log L ≤ (7/10)*(j : ℝ) := by
    simpa only [mul_comm (7/10 : ℝ)] using hlog.trans
      (mul_le_mul_of_nonneg_left two (Nat.cast_nonneg j))
  have hs := pow_le_pow_left₀ (Real.log_nonneg one) upper 2
  have harm := HarmonicSharp39.actual_harmonic_tight L j hi
  unfold coefficient
  linarith only [harm,upper,hs]

theorem coefficient_fringe {L : ℕ} (pos : 1 ≤ L) (hi : L < 2^14) : coefficient L ≤ 59 :=
  (coeff_le pos hi).trans (by norm_num)

/-- The original, unrefined recovery profile suffices for the final
two size bounds after the eight-per-ground estimate. -/
theorem axes_of_raw {N L : ℕ} {w e : ℝ} (lo : 19227 ≤ N) (hi : N < 2^16)
    (pos : 1 ≤ L) (lN : L ≤ N) (hw : 0 ≤ w) (omitted : e ≤ 8*N)
    (raw : (114959/80000)*(L : ℝ)^2-(329/200)*L*w+w^2/2 ≤
      (Harmonic N+433/100)*N + coefficient L*L + Harmonic N*w + 872 + e) :
    (L : ℝ) < N/6 ∧ w < (N : ℝ)/4 := by
  have nlo : (19227 : ℝ) ≤ N := by exact_mod_cast lo
  have hN : Harmonic N ≤ 1173/100 := (HarmonicSharp39.actual_harmonic_tight N 16 hi).trans
    (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg N)
  have hw' := mul_le_mul_of_nonneg_right hN hw
  have coarse : coefficient L ≤ 74 := (coeff_le pos (lN.trans_lt hi)).trans (by norm_num)
  have cl := mul_le_mul_of_nonneg_right coarse (Nat.cast_nonneg L)
  have left : (L : ℝ) < N/6 := RootWidth20258.coarse_left (w := w) nlo (Nat.cast_nonneg L)
    (by nlinarith only [raw,omitted,hm,hw',cl,hw,Nat.cast_nonneg (α := ℝ) N])
  have l6 : 6*L < N := by
    exact_mod_cast (show 6*(L : ℝ) < N by linarith only [left])
  have fine := coefficient_fringe pos (by omega : L < 2^14)
  have fl := mul_le_mul_of_nonneg_right fine (Nat.cast_nonneg (α := ℝ) L)
  refine ⟨left,?_⟩
  by_cases early : N < 20000
  · have hn : Harmonic N ≤ 1103/100 :=
      (HarmonicSharp39.actual_harmonic_tight N 15 (by omega)).trans (by norm_num)
    exact RootWidth20258.fine_width_early (l := (L : ℝ)) nlo hw
      (by nlinarith only [raw,omitted,fl,mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (α := ℝ) N),
        mul_le_mul_of_nonneg_right hn hw])
  · have later : (20000 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_not_gt early)
    exact RootWidth20258.fine_width (l := (L : ℝ)) later hw
      (by nlinarith only [raw,omitted,hm,hw',fl,hw,Nat.cast_nonneg (α := ℝ) N,
        Nat.cast_nonneg (α := ℝ) L])

#print axioms axes_of_raw
end
end JSP233.DyadicWidth20258
