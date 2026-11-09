module

public import Erdos272.Arithmetic.MixedFloor29
public import Erdos272.Core.LongCore34
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual finite coprime supply with squarefree support, including intervals.
The error counts nonzero Mobius coefficients, not all divisors. -/
namespace JSP233.SquarefreeSupply35
open scoped Classical BigOperators
open ArithmeticFunction TotientFloor29 MixedFloor29
noncomputable section

def IntervalCoprime (m A B : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter (fun i => Nat.Coprime i m)

theorem squarefree_divisor_card (m : ℕ) (hm : m≠0) :
    (m.divisors.filter Squarefree).card=2^m.primeFactors.card := by
  have hh := Nat.sum_divisors_filter_squarefree (n:=m) hm (f:=fun _ => (1:ℕ))
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_powerset,
    Nat.factors_eq,List.toFinset_coe,Nat.toFinset_factors,Nat.cast_id] using hh

theorem actual_moebius_error (m : ℕ) (hm : 0<m) :
    divisorError m=(2^m.primeFactors.card:ℕ) := by
  have hmu : ∀ d, |(moebius d:ℝ)|=if Squarefree d then 1 else 0 := by
    intro d
    exact_mod_cast (abs_moebius (n:=d))
  simp_rw [divisorError,hmu]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,squarefree_divisor_card m (by omega)]

theorem actual_prefix_error (m k : ℕ) (hm : 0<m) :
    |(CoprimeCount k m:ℝ)-(k:ℝ)*Nat.totient m/m|≤(2^m.primeFactors.card:ℕ) := by
  have he : (CoprimeCount k m:ℝ)-(k:ℝ)*Nat.totient m/m=
      ∑ d∈m.divisors, (moebius d:ℝ)*(((k/d:ℕ):ℝ)-(k:ℝ)/d) := by
    have hphi : (k:ℝ)*Nat.totient m/m=(k:ℝ)*
        ∑ d∈m.divisors,(moebius d:ℝ)/d := by
      rw [←normalized_totient_identity m hm]
      ring
    rw [coprimeCount_floor k m hm,hphi]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he,←actual_moebius_error m hm]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  have hdiv := nat_div_bounds k d (Nat.pos_of_mem_divisors hd)
  have he' : |((k/d:ℕ):ℝ)-(k:ℝ)/d|≤1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he' (abs_nonneg (moebius d:ℝ))

theorem actual_interval_partition (m A B : ℕ) (hAB : A≤B) :
    (IntervalCoprime m A B).card+CoprimeCount A m=CoprimeCount B m := by
  have hd : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Ioc.mp hj
    omega
  have hu : Finset.Icc 1 A∪Finset.Ioc A B=Finset.Icc 1 B := by
    ext i
    simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hh := Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
    (p:=fun i => Nat.Coprime i m) (q:=fun i => Nat.Coprime i m) hd)
  rw [←Finset.filter_union,hu] at hh
  simpa only [IntervalCoprime,CoprimeCount,Nat.Coprime,add_comm] using hh.symm

theorem actual_interval_error (m A B : ℕ) (hm : 0<m) (hAB : A≤B) :
    |((IntervalCoprime m A B).card:ℝ)-((B:ℝ)-A)*Nat.totient m/m|≤
      2*(2^m.primeFactors.card:ℕ) := by
  have hp : ((IntervalCoprime m A B).card:ℝ)+(CoprimeCount A m:ℝ)=CoprimeCount B m :=
    by exact_mod_cast actual_interval_partition m A B hAB
  have hA := abs_le.mp (actual_prefix_error m A hm)
  have hB := abs_le.mp (actual_prefix_error m B hm)
  rw [sub_mul,sub_div]
  apply abs_le.mpr
  constructor <;> nlinarith only [hp,hA.1,hA.2,hB.1,hB.2]

theorem actual_interval_omega_lower (m A B : ℕ) (hm : 0<m) (hAB : A≤B) :
    B-A≤(m.primeFactors.card+1)*((IntervalCoprime m A B).card+2*2^m.primeFactors.card) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hratio : (1:ℝ)≤((m.primeFactors.card:ℝ)+1)*Nat.totient m/m := by
    apply (le_div_iff₀ hmR).mpr
    simpa only [one_mul] using (show (m:ℝ)≤((m.primeFactors.card:ℝ)+1)*Nat.totient m by
      exact_mod_cast LongCore34.le_prime_factor_count_mul_totient m)
  have he := (abs_le.mp (actual_interval_error m A B hm hAB)).1
  have hl : (0:ℝ)≤(B:ℝ)-A := sub_nonneg.mpr (by exact_mod_cast hAB)
  have ht := mul_le_mul_of_nonneg_left hratio hl
  have hres : (B:ℝ)-A≤((m.primeFactors.card:ℝ)+1)*
      ((IntervalCoprime m A B).card+2*(2^m.primeFactors.card:ℕ)) := by
    have hc := mul_le_mul_of_nonneg_left (show ((B:ℝ)-A)*Nat.totient m/m≤
      (IntervalCoprime m A B).card+2*(2^m.primeFactors.card:ℕ) by linarith)
      (by positivity : (0:ℝ)≤(m.primeFactors.card:ℝ)+1)
    calc
      (B:ℝ)-A=((B:ℝ)-A)*1 := by ring
      _≤((B:ℝ)-A)*(((m.primeFactors.card:ℝ)+1)*Nat.totient m/m) := ht
      _=((m.primeFactors.card:ℝ)+1)*(((B:ℝ)-A)*Nat.totient m/m) := by ring
      _≤_ := hc
  have hcast : ((B-A:ℕ):ℝ)≤(((m.primeFactors.card+1)*
      ((IntervalCoprime m A B).card+2*2^m.primeFactors.card):ℕ):ℝ) := by
    simpa only [Nat.cast_sub hAB,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hres
  exact_mod_cast hcast

theorem actual_half_interval_supply (m K w : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤w) (hK : 8*(w+1)*2^w≤K) :
    K≤4*(w+1)*(IntervalCoprime m (K/2) K).card := by
  have hrow := actual_interval_omega_lower m (K/2) K hm (Nat.div_le_self _ _)
  have hwexp := Nat.pow_le_pow_right (by decide : 1≤2) hw
  have hh := Nat.mul_le_mul (Nat.add_le_add_right hw 1)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hwexp)
      (IntervalCoprime m (K/2) K).card)
  have hhalf : K≤2*(K-K/2) := by omega
  nlinarith

#print axioms squarefree_divisor_card
#print axioms actual_moebius_error
#print axioms actual_prefix_error
#print axioms actual_interval_partition
#print axioms actual_interval_error
#print axioms actual_interval_omega_lower
#print axioms actual_half_interval_supply
end
end JSP233.SquarefreeSupply35
