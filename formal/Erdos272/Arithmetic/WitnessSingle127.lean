module

public import Erdos272.Arithmetic.SingleTangent127
public import Erdos272.Arithmetic.PrefixSuper127

@[expose] public section
namespace JSP233.WitnessSingle127
open StarCompletion RestrictedWitness44 DivisorMoment45
open HarmonicAbel29 SimplexMoment57 TwoSidedMoment62 DivisorMoment122
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def FullFee : ℝ := SingleTangent127.Intercept
theorem full_fee_identity : FullFee=(4755141098:ℝ) := by
  norm_num [FullFee,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]
theorem actual_prefix_exception_single {X N : ℕ} (hXN : X≤N) (_hN : 1≤N) :
    PrefixException X≤
      (X:ℝ)*(Q3 (Real.log N)+2*Harmonic N-SingleTangent127.Slope)+
        SingleTangent127.Intercept := by
  by_cases hX : X=0
  · simp [hX,PrefixException,SingleTangent127.Intercept,LogAnchor127.AnchorIntercept]
  have hX1 : 1≤X := by omega
  have hlogX : 0≤Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
  have hlog : Real.log (X:ℝ)≤Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0<X by omega)) (by exact_mod_cast hXN)
  have hm := SingleTangent127.actual_divisor_second_moment_single_exclusion X
  have hu := div_count_three_prefix hX1
  have hf := actual_divisor_first_moment X
  have hp := mul_le_mul_of_nonneg_left (q3_monotone hlogX hlog) (Nat.cast_nonneg X)
  have hh := mul_le_mul_of_nonneg_left (harmonic_mono hXN) (Nat.cast_nonneg (α:=ℝ) X)
  dsimp only [PrefixException]
  nlinarith only [hm,hu,hf,hp,hh]


theorem actual_exception_prefix127 {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)+2*Harmonic N-SingleTangent127.Slope)+FullFee := by
  have hcG := (mem_ground N c).mp hc
  have hN : 1≤N := by omega
  exact (PrefixSuper127.actual_exception_whole_prefix hc).trans
    (actual_prefix_exception_single (show N≤N from le_rfl) hN)

theorem actual_bad_members_prefix127 {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    ((BadMembers F c P).card:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)+2*Harmonic N-SingleTangent127.Slope)+FullFee := by
  have hh : ((BadMembers F c P).card:ℝ)≤(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_restricted_bad_family_bound c P hF
  exact hh.trans (actual_exception_prefix127 hc)
#print axioms full_fee_identity
#print axioms actual_prefix_exception_single
#print axioms actual_exception_prefix127
#print axioms actual_bad_members_prefix127
end
end JSP233.WitnessSingle127
