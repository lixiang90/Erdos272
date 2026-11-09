module

public import Erdos272.Traces.SquarefreeSupply35
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! A single finite interval sieve: floor errors are subtracted before
taking absolute values, so the error is 2^omega, with no factor two. -/
namespace JSP233.SharpInterval36
open scoped Classical BigOperators
open ArithmeticFunction TotientFloor29 MixedFloor29 SquarefreeSupply35
noncomputable section

theorem interval_floor_error (A B d : ℕ) (hd : 0<d) :
    |(((B/d:ℕ):ℝ)-((A/d:ℕ):ℝ))-((B:ℝ)-A)/d|≤1 := by
  have hA := nat_div_bounds A d hd
  have hB := nat_div_bounds B d hd
  rw [sub_div]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem actual_interval_error_sharp (m A B : ℕ) (hm : 0<m) (hAB : A≤B) :
    |((IntervalCoprime m A B).card:ℝ)-((B:ℝ)-A)*Nat.totient m/m|≤
      (2^m.primeFactors.card:ℕ) := by
  have hp : ((IntervalCoprime m A B).card:ℝ)+(CoprimeCount A m:ℝ)=CoprimeCount B m :=
    by exact_mod_cast actual_interval_partition m A B hAB
  have he : ((IntervalCoprime m A B).card:ℝ)-((B:ℝ)-A)*Nat.totient m/m=
      ∑ d∈m.divisors,(moebius d:ℝ)*
        ((((B/d:ℕ):ℝ)-((A/d:ℕ):ℝ))-((B:ℝ)-A)/d) := by
    have hcard : ((IntervalCoprime m A B).card:ℝ)=
        (CoprimeCount B m:ℝ)-(CoprimeCount A m:ℝ) := by linarith
    have hphi : ((B:ℝ)-A)*Nat.totient m/m=((B:ℝ)-A)*
        ∑ d∈m.divisors,(moebius d:ℝ)/d := by
      rw [←normalized_totient_identity m hm]
      ring
    rw [hcard,coprimeCount_floor B m hm,coprimeCount_floor A m hm,hphi,
      Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he,←actual_moebius_error m hm]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (interval_floor_error A B d (Nat.pos_of_mem_divisors hd)) (abs_nonneg (moebius d:ℝ))

theorem actual_interval_omega_lower_sharp (m A B : ℕ) (hm : 0<m) (hAB : A≤B) :
    B-A≤(m.primeFactors.card+1)*((IntervalCoprime m A B).card+2^m.primeFactors.card) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hratio : (1:ℝ)≤((m.primeFactors.card:ℝ)+1)*Nat.totient m/m := by
    apply (le_div_iff₀ hmR).mpr
    simpa only [one_mul] using (show (m:ℝ)≤((m.primeFactors.card:ℝ)+1)*Nat.totient m by
      exact_mod_cast LongCore34.le_prime_factor_count_mul_totient m)
  have he := (abs_le.mp (actual_interval_error_sharp m A B hm hAB)).1
  have hl : (0:ℝ)≤(B:ℝ)-A := sub_nonneg.mpr (by exact_mod_cast hAB)
  have ht := mul_le_mul_of_nonneg_left hratio hl
  have hres : (B:ℝ)-A≤((m.primeFactors.card:ℝ)+1)*
      ((IntervalCoprime m A B).card+(2^m.primeFactors.card:ℕ)) := by
    have hc := mul_le_mul_of_nonneg_left (show ((B:ℝ)-A)*Nat.totient m/m≤
      (IntervalCoprime m A B).card+(2^m.primeFactors.card:ℕ) by linarith)
      (by positivity : (0:ℝ)≤(m.primeFactors.card:ℝ)+1)
    calc
      (B:ℝ)-A=((B:ℝ)-A)*1 := by ring
      _≤((B:ℝ)-A)*(((m.primeFactors.card:ℝ)+1)*Nat.totient m/m) := ht
      _=((m.primeFactors.card:ℝ)+1)*(((B:ℝ)-A)*Nat.totient m/m) := by ring
      _≤_ := hc
  have hcast : ((B-A:ℕ):ℝ)≤(((m.primeFactors.card+1)*
      ((IntervalCoprime m A B).card+2^m.primeFactors.card):ℕ):ℝ) := by
    simpa only [Nat.cast_sub hAB,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hres
  exact_mod_cast hcast

theorem actual_half_interval_supply_sharp (m K w : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤w) (hK : 4*(w+1)*2^w≤K) :
    K≤4*(w+1)*(IntervalCoprime m (K/2) K).card := by
  have hrow := actual_interval_omega_lower_sharp m (K/2) K hm (Nat.div_le_self _ _)
  have hwexp := Nat.pow_le_pow_right (by decide : 1≤2) hw
  have hh := Nat.mul_le_mul (Nat.add_le_add_right hw 1)
    (Nat.add_le_add_left hwexp (IntervalCoprime m (K/2) K).card)
  have hhalf : K≤2*(K-K/2) := by omega
  nlinarith

#print axioms interval_floor_error
#print axioms actual_interval_error_sharp
#print axioms actual_interval_omega_lower_sharp
#print axioms actual_half_interval_supply_sharp
end
end JSP233.SharpInterval36
