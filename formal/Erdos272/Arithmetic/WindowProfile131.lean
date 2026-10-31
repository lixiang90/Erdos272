import Erdos272.Resources.PairRecovery131
namespace JSP233.WindowProfile131
open StarCompletion RestrictedWitness44 DivisorMoment45 HarmonicAbel29
open SimplexMoment57 TwoSidedMoment62 PairRecovery131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def WindowC (a b s F q L:ℝ) : ℝ :=
  2*L^2+(667/50+a)*L+144579/4000+b+s/q+F

theorem fixed_nonnegative_bound {lo N:ℕ} {f:ℝ}
    (hlo:0<lo) (hloN:lo≤N) (hf:0≤f) : f≤(N:ℝ)*(f/(lo:ℝ)) := by
  have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
  have hle : (lo:ℝ)≤N := by exact_mod_cast hloN
  calc
    f=(lo:ℝ)*(f/(lo:ℝ)) := by field_simp
    _≤(N:ℝ)*(f/(lo:ℝ)) := mul_le_mul_of_nonneg_right hle (div_nonneg hf hloR.le)

theorem fixed_nonpositive_bound {hi N:ℕ} {f:ℝ}
    (hhi:0<hi) (hNhi:N≤hi) (hf:f≤0) : f≤(N:ℝ)*(f/(hi:ℝ)) := by
  have hhiR : (0:ℝ)<hi := by exact_mod_cast hhi
  have hle : (N:ℝ)≤hi := by exact_mod_cast hNhi
  calc
    f=(hi:ℝ)*(f/(hi:ℝ)) := by field_simp
    _≤(N:ℝ)*(f/(hi:ℝ)) := mul_le_mul_of_nonpos_right hle (div_nonpos_of_nonpos_of_nonneg hf hhiR.le)

theorem signed_fixed_bound {lo hi N:ℕ} (hlo:0<lo)
    (hloN:lo≤N) (hNhi:N≤hi) (f:ℝ) :
    f≤(N:ℝ)*(if 0≤f then f/(lo:ℝ) else f/(hi:ℝ)) := by
  by_cases hf:0≤f
  · rw [if_pos hf]
    exact fixed_nonnegative_bound hlo hloN hf
  · rw [if_neg hf]
    exact fixed_nonpositive_bound (by omega) hNhi (le_of_not_ge hf)

theorem sqrt_ratio_bound {lo N:ℕ} {q s:ℝ} (hloN:lo≤N)
    (hq:0<q) (hqs:q^2≤(lo:ℝ)) (hs:0≤s) :
    Real.sqrt (N:ℝ)*s≤(N:ℝ)*(s/q) := by
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  have hle : (lo:ℝ)≤N := by exact_mod_cast hloN
  have hqN : q^2≤(N:ℝ) := hqs.trans hle
  have hsq := Real.sq_sqrt hN
  have hsn := Real.sqrt_nonneg (N:ℝ)
  have hqS : q≤Real.sqrt (N:ℝ) := by nlinarith only [hq,hqN,hsq,hsn]
  have hm := mul_le_mul_of_nonneg_right hqS hsn
  have hd : Real.sqrt (N:ℝ)≤(N:ℝ)/q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith only [hm,hsq]
  calc
    Real.sqrt (N:ℝ)*s≤((N:ℝ)/q)*s := mul_le_mul_of_nonneg_right hd hs
    _=(N:ℝ)*(s/q) := by ring

theorem actual_witness_moment {N:ℕ} {c:ℤ} (hc:c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)+2*(N:ℝ)*Harmonic N := by
  have hw := PrefixSuper127.actual_exception_whole_prefix hc
  have hf := actual_divisor_first_moment N
  dsimp only [PrefixException] at hw
  nlinarith only [hw,hf]

theorem actual_window_budget {lo hi N:ℕ} {a b s f F q L:ℝ} {c:ℤ}
    (hlo100:100000≤lo) (hlo:lo≤N) (_hhi:N≤hi)
    (hm:(∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)≤
      (N:ℝ)*(a*Real.log (N:ℝ)+b)+Real.sqrt (N:ℝ)*s+f)
    (hlog:Real.log (N:ℝ)≤L) (hL:0≤L) (hq:0<q) (hqs:q^2≤(lo:ℝ))
    (hs:0≤s) (ha:0≤667/50+a) (hf:f≤(N:ℝ)*F) (hc:c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)+(N:ℝ)*Extra N≤
      (N:ℝ)*WindowC a b s F q L := by
  have hN : 100000≤N := hlo100.trans hlo
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hlog0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hsq : (Real.log (N:ℝ))^2≤L^2 := (sq_le_sq₀ hlog0 hL).mpr hlog
  have hquad := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤2*(N:ℝ) by positivity)
  have hlinear := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog ha) hN0
  have hsqrt := sqrt_ratio_bound hlo hq hqs hs
  have hw := actual_witness_moment hc
  have he := mul_le_mul_of_nonneg_left (extra_harmonic_upper hN) hN0
  dsimp only [WindowC]
  nlinarith only [hw,hm,he,hquad,hlinear,hsqrt,hf]

theorem actual_window_certificate {lo hi N:ℕ} {a b s f F q L:ℝ}
    (hlo100:100000≤lo) (hlo:lo≤N) (hhi:N≤hi)
    (hm:(∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)≤
      (N:ℝ)*(a*Real.log (N:ℝ)+b)+Real.sqrt (N:ℝ)*s+f)
    (hlog:Real.log (N:ℝ)≤L) (hL:0≤L) (hq:0<q) (hqs:q^2≤(lo:ℝ))
    (hs:0≤s) (ha:0≤667/50+a) (hf:f≤(N:ℝ)*F)
    (hcoarse:(32:ℝ)^2*Rho*(WindowC a b s F q L+9677/20)≤(lo:ℝ))
    (hfine:(900/23:ℝ)^2*Rho*WindowC a b s F q L≤(lo:ℝ)) :
    ConstantCertificate N (WindowC a b s F q L) := by
  have hloR : (lo:ℝ)≤N := by exact_mod_cast hlo
  refine ⟨?_,hcoarse.trans hloR,hfine.trans hloR⟩
  intro c hc
  exact actual_window_budget hlo100 hlo hhi hm hlog hL hq hqs hs ha hf hc

#print axioms fixed_nonnegative_bound
#print axioms fixed_nonpositive_bound
#print axioms signed_fixed_bound
#print axioms sqrt_ratio_bound
#print axioms actual_witness_moment
#print axioms actual_window_budget
#print axioms actual_window_certificate
end
end JSP233.WindowProfile131
