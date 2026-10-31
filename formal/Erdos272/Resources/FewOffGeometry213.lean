import Erdos272.Resources.FewOffGeometry212
import Erdos272.Resources.ActualGrid213
namespace JSP233.FewOffGeometry213
open StarCompletion APGeometry ActualGrid212 FewOffGeometry212
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem actual_few_step_domain {N d k : ℕ} {S : Finset ℤ} {a : ℤ}
    (hN : 640000≤N) (hS : S⊆Ground N) (hd : 0<d) (hk11 : k≤11)
    (hdense : (N : ℝ)<(k : ℝ)*S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ)≤(3/5000 : ℝ)*N)
    (hpos : 0<(ActualOffPoints S d a).card) : 2≤d ∧ d≤11 := by
  have hkR : (k : ℝ)≤11 := by exact_mod_cast hk11
  have hm := mul_le_mul_of_nonneg_right hkR (Nat.cast_nonneg S.card : (0 : ℝ)≤S.card)
  have hdZ : (0 : ℤ)<d := by exact_mod_cast hd
  have hh := ActualGrid213.actual_few_positive_off_step_range hN hS hdZ (hdense.trans_le hm) hfew hpos
  exact_mod_cast hh


#print axioms actual_few_step_domain
end
end JSP233.FewOffGeometry213
