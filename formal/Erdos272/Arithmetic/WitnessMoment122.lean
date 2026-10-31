import Erdos272.Arithmetic.DivisorMoment122
import Erdos272.Arithmetic.TwoSidedMoment62

/-! Full physical left/right distance prefixes with the corrected divisor
second moment. Zero-length sides are included; the actual ground-set root
supplies positivity of N. No assumed exception or family-capacity budget. -/
namespace JSP233.WitnessMoment122
open StarCompletion RestrictedWitness44 DivisorMoment45
open HarmonicAbel29 SimplexMoment57 TwoSidedMoment62 DivisorMoment122
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_prefix_exception_prefix {X N : ℕ} (hXN : X≤N) (_hN : 1≤N) :
    PrefixException X≤(X:ℝ)*(Q3 (Real.log N)+2*Harmonic N) := by
  by_cases hX : X=0
  · simp [hX,PrefixException]
  have hX1 : 1≤X := by omega
  have hlogX : 0≤Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
  have hlog : Real.log (X:ℝ)≤Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0<X by omega)) (by exact_mod_cast hXN)
  have hp := q3_monotone hlogX hlog
  have hm := actual_divisor_second_moment_prefix hX1
  have hf := actual_divisor_first_moment X
  have hh := harmonic_mono hXN
  dsimp only [PrefixException]
  calc
    _≤(X:ℝ)*Q3 (Real.log (X:ℝ))+2*((X:ℝ)*Harmonic X) := by linarith only [hm,hf]
    _≤(X:ℝ)*Q3 (Real.log N)+2*((X:ℝ)*Harmonic N) := by gcongr
    _=_ := by ring

theorem actual_two_sided_exception_prefix {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      ((N-1:ℕ):ℝ)*(Q3 (Real.log N)+2*Harmonic N) := by
  have hcG := (mem_ground N c).mp hc
  have hN : 1≤N := by omega
  have hl := actual_prefix_exception_prefix (show c.toNat-1≤N by omega) hN
  have hr := actual_prefix_exception_prefix (show N-c.toNat≤N by omega) hN
  have hlen : c.toNat-1+(N-c.toNat)=N-1 := by omega
  rw [actual_exception_split hc]
  calc
    _≤((c.toNat-1:ℕ):ℝ)*(Q3 (Real.log N)+2*Harmonic N)+
        ((N-c.toNat:ℕ):ℝ)*(Q3 (Real.log N)+2*Harmonic N) := add_le_add hl hr
    _=((c.toNat-1+(N-c.toNat):ℕ):ℝ)*(Q3 (Real.log N)+2*Harmonic N) := by push_cast;ring
    _=_ := by rw [hlen]

theorem actual_exception_prefix122 {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*(Q3 (Real.log N)+2*Harmonic N) := by
  have hcG := (mem_ground N c).mp hc
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hcoef : 0≤Q3 (Real.log N)+2*Harmonic N :=
    add_nonneg (q3_nonnegative hlog) (mul_nonneg (by norm_num) (harmonic_nonneg N))
  exact (actual_two_sided_exception_prefix hc).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N-1≤N by omega)) hcoef)

theorem actual_bad_members_prefix122 {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    ((BadMembers F c P).card:ℝ)≤(N:ℝ)*(Q3 (Real.log N)+2*Harmonic N) := by
  have hh : ((BadMembers F c P).card:ℝ)≤(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_restricted_bad_family_bound c P hF
  exact hh.trans (actual_exception_prefix122 hc)

#print axioms actual_prefix_exception_prefix
#print axioms actual_two_sided_exception_prefix
#print axioms actual_exception_prefix122
#print axioms actual_bad_members_prefix122
end
end JSP233.WitnessMoment122
