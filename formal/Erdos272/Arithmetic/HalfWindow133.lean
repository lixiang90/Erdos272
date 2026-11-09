module

public import Erdos272.Arithmetic.HalfPrefix133
public import Erdos272.Arithmetic.WindowProfile131
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.HalfWindow133
open StarCompletion RestrictedWitness44 DivisorMoment45 HarmonicAbel29
open SimplexMoment57 TwoSidedMoment62 PairRecovery131 WindowProfile131
open HalfBad133 HalfPrefix133
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def HalfWindowC (a b s F q L:ℝ) : ℝ :=
  2*L^2+(321/25+a/2)*L+4482/125+b/2+s/(2*q)+F/2

theorem extra_half_harmonic_upper {N:ℕ} (hN:100000≤N) :
    Extra N+(3/2)*Harmonic N≤
      2*(Real.log N)^2+(321/25)*Real.log N+4482/125 := by
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  dsimp only [Extra]
  nlinarith only [hh]

theorem actual_half_window_budget {lo hi N:ℕ} {a b s f F q L:ℝ} {c:ℤ}
    (hlo100:100000≤lo) (hlo:lo≤N) (_hhi:N≤hi)
    (hm:(∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)≤
      (N:ℝ)*(a*Real.log (N:ℝ)+b)+Real.sqrt (N:ℝ)*s+f)
    (hlog:Real.log (N:ℝ)≤L) (hL:0≤L) (hq:0<q) (hqs:q^2≤(lo:ℝ))
    (hs:0≤s) (ha:0≤321/25+a/2) (hf:f≤(N:ℝ)*F) (hc:c∈Ground N) :
    (HalfWitnessException (Ground N) c:ℝ)+(N:ℝ)*Extra N≤
      (N:ℝ)*HalfWindowC a b s F q L := by
  have hN : 100000≤N := hlo100.trans hlo
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hlog0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hsq : (Real.log (N:ℝ))^2≤L^2 := (sq_le_sq₀ hlog0 hL).mpr hlog
  have hquad := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤2*(N:ℝ) by positivity)
  have hlinear := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog ha) hN0
  have hsqrt := sqrt_ratio_bound hlo hq hqs hs
  have hw := actual_half_witness_moment hc
  have he := mul_le_mul_of_nonneg_left (extra_half_harmonic_upper hN) hN0
  have hquot : s/(2*q)=(s/q)/2 := by field_simp [hq.ne']
  dsimp only [HalfWindowC]
  rw [hquot]
  nlinarith only [hw,hm,he,hquad,hlinear,hsqrt,hf]

#print axioms extra_half_harmonic_upper
#print axioms actual_half_window_budget
end
end JSP233.HalfWindow133
