import Erdos272.Traces.SquarefreeSupply35

/-! The two floors in a genuine half interval are coupled.  Twice the
count has squarefree error 2^omega, so no rounding error is paid twice. -/
namespace JSP233.HalfInterval37
open scoped Classical BigOperators
open ArithmeticFunction TotientFloor29 MixedFloor29 SquarefreeSupply35
noncomputable section

theorem half_div_identity (K d : ℕ) : (K/2)/d=(K/d)/2 := by
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem half_floor_scaled_error (K d : ℕ) (hd : 0<d) :
    |2*((K/d:ℕ):ℝ)-2*(((K/2)/d:ℕ):ℝ)-(K:ℝ)/d|≤1 := by
  have hb := nat_div_bounds K d hd
  have hi := half_div_identity K d
  have hn : 2*((K/2)/d)≤K/d ∧ K/d≤2*((K/2)/d)+1 := by
    rw [hi]
    omega
  have hl : (2:ℝ)*(((K/2)/d:ℕ):ℝ)≤((K/d:ℕ):ℝ) := by exact_mod_cast hn.1
  have hu : ((K/d:ℕ):ℝ)≤2*(((K/2)/d:ℕ):ℝ)+1 := by exact_mod_cast hn.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem actual_half_interval_scaled_error (m K : ℕ) (hm : 0<m) :
    |2*((IntervalCoprime m (K/2) K).card:ℝ)-(K:ℝ)*Nat.totient m/m|≤
      (2^m.primeFactors.card:ℕ) := by
  have hp : ((IntervalCoprime m (K/2) K).card:ℝ)+(CoprimeCount (K/2) m:ℝ)=
      CoprimeCount K m := by
    exact_mod_cast actual_interval_partition m (K/2) K (Nat.div_le_self _ _)
  have he : 2*((IntervalCoprime m (K/2) K).card:ℝ)-(K:ℝ)*Nat.totient m/m=
      ∑ d∈m.divisors,(moebius d:ℝ)*
        (2*((K/d:ℕ):ℝ)-2*(((K/2)/d:ℕ):ℝ)-(K:ℝ)/d) := by
    have hc : ((IntervalCoprime m (K/2) K).card:ℝ)=
        (CoprimeCount K m:ℝ)-(CoprimeCount (K/2) m:ℝ) := by linarith
    have hf : (K:ℝ)*Nat.totient m/m=(K:ℝ)*
        ∑ d∈m.divisors,(moebius d:ℝ)/d := by
      rw [←normalized_totient_identity m hm]
      ring
    rw [hc,coprimeCount_floor K m hm,coprimeCount_floor (K/2) m hm,hf,
      mul_sub,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
      ←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he,←actual_moebius_error m hm]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (half_floor_scaled_error K d (Nat.pos_of_mem_divisors hd)) (abs_nonneg (moebius d:ℝ))

theorem actual_half_interval_ratio_lower (m K R : ℕ) (hm : 0<m)
    (hR : m≤R*Nat.totient m) :
    K≤R*(2*(IntervalCoprime m (K/2) K).card+2^m.primeFactors.card) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hr : (1:ℝ)≤(R:ℝ)*Nat.totient m/m := by
    apply (le_div_iff₀ hmR).mpr
    simpa only [one_mul] using
      (show (m:ℝ)≤(R:ℝ)*Nat.totient m by exact_mod_cast hR)
  have he := (abs_le.mp (actual_half_interval_scaled_error m K hm)).1
  have hk := mul_le_mul_of_nonneg_left hr (show (0:ℝ)≤K by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (show (K:ℝ)*Nat.totient m/m≤2*(IntervalCoprime m (K/2) K).card+
      (2^m.primeFactors.card:ℕ) by linarith) (show (0:ℝ)≤R by positivity)
  have hout : (K:ℝ)≤(R:ℝ)*(2*(IntervalCoprime m (K/2) K).card+
      (2^m.primeFactors.card:ℕ)) := by
    calc
      (K:ℝ)=(K:ℝ)*1 := by ring
      _≤(K:ℝ)*((R:ℝ)*Nat.totient m/m) := hk
      _=(R:ℝ)*((K:ℝ)*Nat.totient m/m) := by ring
      _≤_ := hh
  exact_mod_cast hout

theorem actual_half_interval_ratio_supply (m K R w : ℕ) (hm : 0<m)
    (hR : m≤R*Nat.totient m) (hw : m.primeFactors.card≤w)
    (hK : 2*R*2^w≤K) :
    K≤4*R*(IntervalCoprime m (K/2) K).card := by
  have he := actual_half_interval_ratio_lower m K R hm hR
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hw
  have ht := Nat.mul_le_mul_left R hp
  nlinarith

theorem actual_half_interval_omega_supply (m K w : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤w) (hK : 2*(w+1)*2^w≤K) :
    K≤4*(w+1)*(IntervalCoprime m (K/2) K).card := by
  apply actual_half_interval_ratio_supply m K (w+1) w hm _ hw hK
  exact (LongCore34.le_prime_factor_count_mul_totient m).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hw 1))

#print axioms half_div_identity
#print axioms half_floor_scaled_error
#print axioms actual_half_interval_scaled_error
#print axioms actual_half_interval_ratio_lower
#print axioms actual_half_interval_ratio_supply
#print axioms actual_half_interval_omega_supply
end
end JSP233.HalfInterval37
