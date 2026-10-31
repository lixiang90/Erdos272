import Erdos272.Arithmetic.DirectMoment130
import Erdos272.Arithmetic.DirectGate130
import Erdos272.Arithmetic.HarmonicCorrect118
namespace JSP233.ProfilePayment130
open StarCompletion RestrictedWitness44 DivisorMoment45
open DivisorMoment122 DirectMoment130 HarmonicAbel29
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem direct_core_harmonic_le {N:ℕ} (hN:100000≤N) :
    (Q3 (Real.log N)-ELower (Real.log N)+2*Harmonic N)+2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+597/20≤P (Real.log N) := by
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hp := direct_polynomial_upper hlog
  dsimp only [PBase,Q3] at hp ⊢
  nlinarith only [hh,hp]

theorem actual_exception_profile {N:ℕ} {c:ℤ} (hN:100000≤N) (hc:c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)+(N:ℝ)*(2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+597/20)≤(N:ℝ)*P (Real.log N) := by
  have he := actual_witness_Elower (by omega : 44100≤N) hc
  have hp := mul_le_mul_of_nonneg_left (direct_core_harmonic_le hN) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [he,hp]

theorem actual_bad_members_profile {N:ℕ} {F:Finset (Finset ℤ)}
    (hN:100000≤N) (c:ℤ) (T:Finset ℤ) (hc:c∈Ground N) (hF:Legal (Ground N) F) :
    ((BadMembers F c T).card:ℝ)+(N:ℝ)*(2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+597/20)≤(N:ℝ)*P (Real.log N) := by
  have hh : ((BadMembers F c T).card:ℝ)≤(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_restricted_bad_family_bound c T hF
  have hp := actual_exception_profile hN hc
  linarith only [hh,hp]

theorem gate_polynomial_identity (x:ℝ) : P x=DirectGate130.P x := rfl
#print axioms direct_core_harmonic_le
#print axioms actual_exception_profile
#print axioms actual_bad_members_profile
#print axioms gate_polynomial_identity
end
end JSP233.ProfilePayment130
