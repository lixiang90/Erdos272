module

public import Erdos272.Resources.IntegerUniformProfiles209
public import Erdos272.Arithmetic.HarmonicLog55

@[expose] public section

namespace JSP233.IntegerLightLog209
open IntegerUniformProfiles209 IntegerUniformRows209 IntegerHighPrices209
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def J (w : Fin 11) : ℕ := if w.val<4 then 14 else 18
def LogCap (w : Fin 11) : ℕ := if w.val<4 then 10 else 13
def Facts (w : Fin 11) : Prop :=
  ∀i : Fin (count w),∀b : Fin 7,
    Upper w≤2^(J w)*((band (row w i.val) b).T-(band (row w i.val) b).E)
instance (w : Fin 11) : Decidable (Facts w) := by unfold Facts;infer_instance

theorem facts (w : Fin 11) : Facts w := by
  fin_cases w <;> decide +kernel
theorem log_two_budget (w : Fin 11) :
    (J w : ℝ)*(173287/250000)≤(LogCap w : ℝ) := by
  fin_cases w <;> norm_num [J,LogCap]

theorem ratio_bound {H A j : ℕ} (hH : 0<H) (hA : 0<A) (hHA : H≤2^j*A) :
    Real.log ((H : ℝ)/A)≤(j : ℝ)*(173287/250000) := by
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  have hAr : (0 : ℝ)<A := by exact_mod_cast hA
  have hprod : (H : ℝ)≤(2 : ℝ)^j*A := by exact_mod_cast hHA
  have hdiv : (H : ℝ)/A≤(2 : ℝ)^j := (div_le_iff₀ hAr).mpr hprod
  have hh := Real.log_le_log (div_pos hHr hAr) hdiv
  rw [Real.log_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left HarmonicLog55.actual_log_two_upper (Nat.cast_nonneg j))

theorem actual_log_cap (w : Fin 11) (i : Fin (count w)) (b : Fin 7) :
    Real.log ((Upper w : ℝ)/((band (row w i.val) b).T-(band (row w i.val) b).E : ℕ))≤
      (LogCap w : ℝ) := by
  have hw := IntegerUniformRows209.facts (W_mem w) (row_mem w i)
  have hb := hw.2.2.2.2.2.2.1 b
  have hm : (row w i.val).e<(W w).M := hw.2.2.1
  have hA : 0<(band (row w i.val) b).T-(band (row w i.val) b).E := by
    have ht := hb.1
    have he := hb.2.2.1
    omega
  have hH : 0<Upper w := by have hh:=data_range w;omega
  exact (ratio_bound hH hA (facts w i b)).trans (log_two_budget w)

#print axioms facts
#print axioms ratio_bound
#print axioms actual_log_cap
end
end JSP233.IntegerLightLog209
