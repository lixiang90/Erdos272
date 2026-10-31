import Erdos272.Arithmetic.HalfWindow133
import Erdos272.Resources.HalfRecovery133

namespace JSP233.HalfWindowCertificate137
open StarCompletion RestrictedWitness44 DivisorMoment45 HarmonicAbel29
open SimplexMoment57 TwoSidedMoment62 PairRecovery131 WindowProfile131
open HalfBad133 HalfWindow133
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def HalfConstantCertificate (N : ℕ) (C : ℝ) : Prop :=
  (∀c∈Ground N,(HalfWitnessException (Ground N) c:ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) ∧
  (32:ℝ)^2*Rho*(C+9677/20)≤(N:ℝ) ∧
  (37:ℝ)^2*Rho*C≤(N:ℝ)

theorem actual_half_window_certificate {lo hi N:ℕ} {a b s f F q L:ℝ}
    (hlo100:100000≤lo) (hlo:lo≤N) (hhi:N≤hi)
    (hm:(∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)≤
      (N:ℝ)*(a*Real.log (N:ℝ)+b)+Real.sqrt (N:ℝ)*s+f)
    (hlog:Real.log (N:ℝ)≤L) (hL:0≤L) (hq:0<q) (hqs:q^2≤(lo:ℝ))
    (hs:0≤s) (ha:0≤321/25+a/2) (hf:f≤(N:ℝ)*F)
    (hcoarse:(32:ℝ)^2*Rho*(HalfWindowC a b s F q L+9677/20)≤(lo:ℝ))
    (hfine:(37:ℝ)^2*Rho*HalfWindowC a b s F q L≤(lo:ℝ)) :
    HalfConstantCertificate N (HalfWindowC a b s F q L) := by
  have hloR : (lo:ℝ)≤N := by exact_mod_cast hlo
  refine ⟨?_,hcoarse.trans hloR,hfine.trans hloR⟩
  intro c hc
  exact actual_half_window_budget hlo100 hlo hhi hm hlog hL hq hqs hs ha hf hc

theorem actual_balanced_width_payment {N w : ℕ} {C : ℝ}
    (hgate : (37:ℝ)^2*Rho*C≤(N:ℝ))
    (hwidth : (w:ℝ)^2≤(N:ℝ)*(Rho*C)) : 37*w≤N := by
  have hg := mul_le_mul_of_nonneg_left hgate (Nat.cast_nonneg (α:=ℝ) N)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(37:ℝ)^2)
  have hs : ((37:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hg]
  have hl : (37:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  exact_mod_cast hl

theorem actual_bootstrap_profile_payment {N : ℕ} {D C : ℝ}
    (hgate : (37:ℝ)^2*Rho*C≤(N:ℝ))
    (hprofile : D≤(N:ℝ)*C) : 1369*D≤RawEndpoint112.DeficitCoeff*(N:ℝ)^2 := by
  have hg := mul_le_mul_of_nonneg_left hgate (Nat.cast_nonneg (α:=ℝ) N)
  have hc : 1369*((N:ℝ)*C)≤RawEndpoint112.DeficitCoeff*(N:ℝ)^2 := by
    dsimp only [Rho,RawEndpoint112.DeficitCoeff] at hg ⊢
    nlinarith only [hg]
  exact (mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤1369)).trans hc

#print axioms actual_half_window_certificate
#print axioms actual_balanced_width_payment
#print axioms actual_bootstrap_profile_payment
end
end JSP233.HalfWindowCertificate137
