module

public import Erdos272.Arithmetic.LightPhaseAnalytic209

@[expose] public section

namespace JSP233.LightCoefficient209
open LightPhaseAnalytic209
noncomputable section
set_option maxHeartbeats 0

/-- An integer numerator/denominator for each analytic light coefficient. -/
theorem coeff_nat {V E k : ℕ} (hEV : E<V) (hk : 0<k) :
    Coeff V E k=
      ((V*(V-E)-(V-E-k)^2:ℕ):ℝ)/(2*((V-E:ℕ):ℝ)*(k:ℝ)^2) := by
  have hCV : V-E≤V := Nat.sub_le V E
  have hs : V-E-k≤V-E := Nat.sub_le _ _
  have hnum : (V-E-k)^2≤V*(V-E) := by
    have h1 := Nat.mul_le_mul hs hs
    have h2 := Nat.mul_le_mul_right (V-E) hCV
    nlinarith only [h1,h2]
  have hC : ((V-E:ℕ):ℝ)=(V:ℝ)-E := Nat.cast_sub hEV.le
  have hmax : ((V-E-k:ℕ):ℝ)=max ((V:ℝ)-E-k) 0 := by
    by_cases hkc : k≤V-E
    · rw [Nat.cast_sub hkc,hC,max_eq_left]
      have hr : (k:ℝ)≤(V-E:ℕ) := by exact_mod_cast hkc
      linarith only [hr,hC]
    · have hz : V-E-k=0 := by omega
      rw [hz,Nat.cast_zero,max_eq_right]
      have hr : ((V-E:ℕ):ℝ)≤k := by exact_mod_cast (show V-E≤k by omega)
      linarith only [hr,hC]
  rw [Nat.cast_sub hnum,Nat.cast_mul,Nat.cast_pow,hmax,hC]
  unfold Coeff
  have hCR : (0:ℝ)<(V:ℝ)-E := sub_pos.mpr (by exact_mod_cast hEV)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  field_simp [ne_of_gt hCR,ne_of_gt hkR]
  <;> ring

#print axioms coeff_nat
end
end JSP233.LightCoefficient209
