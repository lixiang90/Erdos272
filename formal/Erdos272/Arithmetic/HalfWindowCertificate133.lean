import Erdos272.Arithmetic.HalfWindow133
import Erdos272.Resources.HalfRecovery133

namespace JSP233.HalfWindowCertificate133
open StarCompletion RestrictedWitness44 DivisorMoment45 HarmonicAbel29
open SimplexMoment57 TwoSidedMoment62 PairRecovery131 WindowProfile131
open HalfBad133 HalfWindow133 HalfRecovery133
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_half_window_certificate {lo hi N:ℕ} {a b s f F q L:ℝ}
    (hlo100:100000≤lo) (hlo:lo≤N) (hhi:N≤hi)
    (hm:(∑d∈Finset.Icc 1 N,(d.divisors.card:ℝ)^2)≤
      (N:ℝ)*(a*Real.log (N:ℝ)+b)+Real.sqrt (N:ℝ)*s+f)
    (hlog:Real.log (N:ℝ)≤L) (hL:0≤L) (hq:0<q) (hqs:q^2≤(lo:ℝ))
    (hs:0≤s) (ha:0≤321/25+a/2) (hf:f≤(N:ℝ)*F)
    (hcoarse:(32:ℝ)^2*Rho*(HalfWindowC a b s F q L+9677/20)≤(lo:ℝ))
    (hfine:(900/23:ℝ)^2*Rho*HalfWindowC a b s F q L≤(lo:ℝ)) :
    HalfConstantCertificate N (HalfWindowC a b s F q L) := by
  have hloR : (lo:ℝ)≤N := by exact_mod_cast hlo
  refine ⟨?_,hcoarse.trans hloR,hfine.trans hloR⟩
  intro c hc
  exact actual_half_window_budget hlo100 hlo hhi hm hlog hL hq hqs hs ha hf hc

#print axioms actual_half_window_certificate
end
end JSP233.HalfWindowCertificate133
