import Erdos272.Arithmetic.HalfInterval37

/-! Real totient-ratio supplies for the actual coupled half interval.
R may be a rational primorial product embedded in the reals. -/
namespace JSP233.TotientRatio38
open scoped Classical
open SquarefreeSupply35 HalfInterval37
noncomputable section

theorem ratio_nonneg {m : ℕ} {R : ℝ} (hm : 0<m)
    (hR : (m:ℝ)≤R*Nat.totient m) : 0≤R := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hp : (0:ℝ)≤Nat.totient m := by positivity
  by_contra hn
  have hnR : R≤0 := le_of_lt (lt_of_not_ge hn)
  have hh := mul_nonpos_of_nonpos_of_nonneg hnR hp
  linarith

theorem actual_half_interval_real_lower (m K : ℕ) (R : ℝ) (hm : 0<m)
    (hR : (m:ℝ)≤R*Nat.totient m) :
    (K:ℝ)≤R*(2*(IntervalCoprime m (K/2) K).card+(2^m.primeFactors.card:ℕ)) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hR0 := ratio_nonneg hm hR
  have hr : (1:ℝ)≤R*Nat.totient m/m := by
    apply (le_div_iff₀ hmR).mpr
    simpa only [one_mul] using hR
  have he := (abs_le.mp (actual_half_interval_scaled_error m K hm)).1
  have hk := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤K by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (show (K:ℝ)*Nat.totient m/m≤2*(IntervalCoprime m (K/2) K).card+
      (2^m.primeFactors.card:ℕ) by linarith) hR0
  calc
    (K:ℝ)=(K:ℝ)*1 := by ring
    _≤(K:ℝ)*(R*Nat.totient m/m) := hk
    _=R*((K:ℝ)*Nat.totient m/m) := by ring
    _≤_ := hh

theorem actual_half_interval_real_supply (m K w : ℕ) (R : ℝ) (hm : 0<m)
    (hR : (m:ℝ)≤R*Nat.totient m) (hw : m.primeFactors.card≤w)
    (hK : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (K:ℝ)≤4*R*(IntervalCoprime m (K/2) K).card := by
  have hr := actual_half_interval_real_lower m K R hm hR
  have hR0 := ratio_nonneg hm hR
  have he : ((2^m.primeFactors.card:ℕ):ℝ)≤(2^w:ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤2) hw
  have hh := mul_le_mul_of_nonneg_left he hR0
  nlinarith only [hr,hh,hK]

#print axioms ratio_nonneg
#print axioms actual_half_interval_real_lower
#print axioms actual_half_interval_real_supply
end
end JSP233.TotientRatio38
