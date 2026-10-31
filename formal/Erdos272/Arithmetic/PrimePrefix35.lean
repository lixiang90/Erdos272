import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite prime-index supplies for the actual variable-anchor coprime rows.
The product may be as large as N²; no bound on its divisor count is assumed. -/
namespace JSP233.PrimePrefix35
open scoped Classical BigOperators
noncomputable section

def CoprimePrefix (m k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter (fun i => Nat.Coprime i m)

theorem prime_count_le_coprime_add_factors (m k : ℕ) (hm : m≠0) :
    Nat.primeCounting k ≤ (CoprimePrefix m k).card + m.primeFactors.card := by
  have hs : Nat.primesLE k ⊆ CoprimePrefix m k ∪ m.primeFactors := by
    intro p hp
    obtain ⟨hpk, hpprime⟩ := Nat.mem_primesLE.mp hp
    by_cases hpm : p∣m
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hpprime,hpm,hm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpprime.one_lt.le,hpk⟩,hpprime.coprime_iff_not_dvd.mpr hpm⟩)
  rw [←Nat.primesLE_card_eq_primeCounting]
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem finite_prime_count (k J : ℕ) (hk : k<2^J) :
    k ≤ J*(Nat.primeCounting k+1) := by
  by_cases hk2 : 2≤k
  · have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hkreal : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
    have hkreal1 : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
    have hp := (div_le_iff₀ (Real.log_pos hkreal1)).mp (Chebyshev.pi_ge k)
    have hlogk : Real.log (k:ℝ) ≤ (J:ℝ)*Real.log 2 := by
      have hh := Real.log_le_log hkreal (show (k:ℝ)≤(2:ℝ)^J by exact_mod_cast hk.le)
      simpa only [Real.log_pow] using hh
    have hlogsucc : Real.log ((k:ℝ)+1) ≤ (J:ℝ)*Real.log 2 := by
      have hh := Real.log_le_log (by positivity : (0:ℝ)<(k:ℝ)+1)
        (show (k:ℝ)+1≤(2:ℝ)^J by exact_mod_cast (by omega : k+1≤2^J))
      simpa only [Real.log_pow] using hh
    have hmul := mul_le_mul_of_nonneg_left hlogk
      (show (0:ℝ)≤Nat.primeCounting k by positivity)
    have hres : (k:ℝ)≤(J:ℝ)*((Nat.primeCounting k:ℝ)+1) := by nlinarith
    exact_mod_cast hres
  · have hJ : k≤J := by
      by_cases hJ0 : J=0
      · subst J; norm_num at hk; omega
      · omega
    have hmul := Nat.mul_le_mul_left J (show 1≤Nat.primeCounting k+1 by omega)
    omega

theorem prime_factor_count_le_log {m : ℕ} (hm : m≠0) :
    m.primeFactors.card≤Nat.log 2 m := by
  apply (Nat.le_log_iff_pow_le (by decide) hm).mpr
  calc
    2^m.primeFactors.card≤∏ p∈m.primeFactors,p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _≤m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

theorem actual_prime_prefix_row_omega (m k J w : ℕ) (hm : 0<m)
    (hk : k<2^J) (hw : m.primeFactors.card≤w) :
    k≤J*((CoprimePrefix m k).card+w+1) := by
  have hpi := prime_count_le_coprime_add_factors m k (by omega)
  exact (finite_prime_count k J hk).trans
    (Nat.mul_le_mul_left J (show Nat.primeCounting k+1≤
      (CoprimePrefix m k).card+w+1 by omega))

theorem trace_row_payment_omega (J w h C W : ℕ)
    (hrow : C≤J*(W+h*(w+1))) (hsize : 2*J*(w+1)*h≤C) :
    C≤2*J*W := by nlinarith

theorem actual_prime_prefix_row (N m k : ℕ) (hm : 0<m) (hmN : m≤N^2)
    (hkN : k≤N) :
    k ≤ (Nat.log 2 N+1)*((CoprimePrefix m k).card+2*(Nat.log 2 N+1)+1) := by
  let J := Nat.log 2 N+1
  have hN : 0<N := by nlinarith
  have hpow : N<2^J := Nat.lt_pow_succ_log_self (by decide) N
  have hmPow : m<2^(2*J) := by
    have hh := Nat.mul_self_lt_mul_self hpow
    have he : 2^J*2^J=2^(2*J) := by rw [←pow_add]; congr 1; omega
    rw [he] at hh
    exact hmN.trans_lt (by simpa only [pow_two] using hh)
  have hfactor : m.primeFactors.card≤2*J := by
    have hh := Nat.log_lt_of_lt_pow (by omega : m≠0) hmPow
    exact (prime_factor_count_le_log (by omega : m≠0)).trans hh.le
  have hpi := prime_count_le_coprime_add_factors m k (by omega)
  have hk := finite_prime_count k J (hkN.trans_lt hpow)
  have hh := Nat.mul_le_mul_left J (show Nat.primeCounting k+1≤
      (CoprimePrefix m k).card+2*J+1 by omega)
  exact hk.trans hh

theorem actual_prime_prefix_sum {α : Type*} (I : Finset α) (k : α→ℕ)
    (N m : ℕ) (hm : 0<m) (hmN : m≤N^2) (hkN : ∀ d∈I,k d≤N) :
    (∑ d∈I,k d) ≤ (Nat.log 2 N+1)*
      ((∑ d∈I,(CoprimePrefix m (k d)).card)+I.card*(2*(Nat.log 2 N+1)+1)) := by
  have hh := Finset.sum_le_sum (fun d hd => actual_prime_prefix_row N m (k d) hm hmN (hkN d hd))
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hh
  nlinarith only [hh]

theorem trace_row_payment (J h C W : ℕ) (hrow : C≤J*(W+h*(2*J+1)))
    (hsize : 2*J*(2*J+1)*h≤C) : C≤2*J*W := by
  nlinarith

theorem triangular_trace_payment (B K h C H : ℕ) (hB : 1≤B)
    (htri : h*(h+1)≤2*C) (hcover : H≤C+h) (hlarge : K≤H)
    (hK : 2*B^2≤K) : B*h≤C ∧ K≤2*C := by
  have hpay : B*h≤C := by
    by_contra hn
    have hpos : 0<h := by
      by_contra hh
      have he : h=0 := by omega
      simp [he] at hn
    have hh : h≤2*B-2 := by
      by_contra hh
      have he : 2*B≤h+1 := by omega
      have hm := Nat.mul_le_mul_left h he
      nlinarith
    have hm := Nat.mul_le_mul_left (B+1) hh
    have he : 2*B-2+2=2*B := by omega
    nlinarith
  constructor
  · exact hpay
  · have hh := Nat.mul_le_mul_right h hB; nlinarith

theorem square_trace_payment (B K h C H : ℕ) (hB : 1≤B)
    (hsquare : h^2≤C) (hcover : H≤C+h) (hlarge : K≤H)
    (hK : B^2≤K) : B*h≤C ∧ K≤2*C := by
  have hpay : B*h≤C := by
    by_contra hn
    have hh : h<B := by
      by_contra hh
      have hm := Nat.mul_le_mul_right h (show B≤h by omega)
      nlinarith
    have hm := Nat.mul_le_mul_left (B+1) (show h≤B-1 by omega)
    have he : B-1+1=B := by omega
    nlinarith
  constructor
  · exact hpay
  · have hh := Nat.mul_le_mul_right h hB; nlinarith

#print axioms prime_count_le_coprime_add_factors
#print axioms finite_prime_count
#print axioms prime_factor_count_le_log
#print axioms actual_prime_prefix_row_omega
#print axioms trace_row_payment_omega
#print axioms actual_prime_prefix_row
#print axioms actual_prime_prefix_sum
#print axioms trace_row_payment
#print axioms triangular_trace_payment
#print axioms square_trace_payment
end
end JSP233.PrimePrefix35
