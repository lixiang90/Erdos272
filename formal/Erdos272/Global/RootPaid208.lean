module

public import Erdos272.Global.RootQuadratic208
public import Erdos272.Arithmetic.DyadicPrice208

@[expose] public section

/-! Actual-root assembly for the final mathematical window.  The only unpaid
input is the explicit bound on the actual avoider subfamily, to be supplied
by the scaled source/near counting theorem.  There is no assumed upper bound
on the full family. -/
namespace JSP233.RootPaid208
open StarCompletion RootQuadratic208 SevenPrices208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_uniform_root_paid {N j : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ}
    (hlo : 659912 ≤ N) (hhi : N ≤ 705097) (hj : 1 ≤ j)
    (hF : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬ IsAP S)
    (hT : T ∈ F) (hTc : c ∉ T)
    (hlower : 242 * 2^j ≤ T.card) (hupper : T.card ≤ 2 * 242 * 2^j)
    (hsparse : 11 * T.card ≤ N)
    (havoid : ((Avoiders F c).card : ℝ) / (N : ℝ)^2 ≤
      UniformG * N / ((2 : ℝ)^j)^3 + UniformU / (2 : ℝ)^j + UniformEta / N) :
    (F.card : ℝ) / (N : ℝ)^2 ≤ Budget - Loss / N := by
  have hscale : 11 * 242 * 2^j ≤ N := by nlinarith only [hlower, hsparse]
  have hindex := actual207_scale_index hhi hscale
  have hr := actual_root_scale_envelope (by omega : 4 ≤ N) hF hbad hT hTc hupper hsparse
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hr
  have hnlo : (659912 : ℝ) ≤ N := by exact_mod_cast hlo
  have hnhi : (N : ℝ) ≤ 705097 := by exact_mod_cast hhi
  have hp := DyadicPrice208.actual_dyadic_window hnlo hnhi hj hindex
  have hpay := actual_partition_payment hr havoid
  dsimp only [DyadicPrice208.Actual, DyadicPrice208.Q, RootQuadratic208.Q] at hp hpay
  linarith only [hp, hpay]

#print axioms actual_uniform_root_paid
end
end JSP233.RootPaid208
