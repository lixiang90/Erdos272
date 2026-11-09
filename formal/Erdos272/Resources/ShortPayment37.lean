module

public import Erdos272.Traces.DyadicTraceSupply36
public import Erdos272.Arithmetic.HarmonicAbel

@[expose] public section

/-! Flexible payment of actual short AP prefixes and a true dyadic harmonic
bound.  No prefix row is forced to spend half of its supply. -/
namespace JSP233.ShortPayment37
open scoped Classical BigOperators
open DyadicTraceSupply36
noncomputable section

theorem weighted_trace_payment (B ell w K h C A : ℕ) (hB : 0<B)
    (hsquare : h^2≤C) (hcover : K≤C+h) (hK : B^2≤K)
    (hrow : C≤ell*(A+h*(w+1))) :
    (B-ell*(w+1))*K≤ell*(B+1)*A := by
  have hp := PrimePrefix35.square_trace_payment B K h C (C+h)
    hB hsquare le_rfl hcover hK
  have hBK : B*K≤(B+1)*C := by nlinarith [Nat.mul_le_mul_left B hcover]
  by_cases hsmall : B≤ell*(w+1)
  · simp [Nat.sub_eq_zero_of_le hsmall]
  have hsub : B-ell*(w+1)+ell*(w+1)=B := Nat.sub_add_cancel (by omega)
  have hrowB := Nat.mul_le_mul_left B hrow
  have hpay := Nat.mul_le_mul_left (ell*(w+1)) hp.1
  have hCA : (B-ell*(w+1))*C≤ell*B*A := by nlinarith only [hrowB,hpay,hsub]
  have hleft := Nat.mul_le_mul_left (B-ell*(w+1)) hBK
  have hright := Nat.mul_le_mul_left (B+1) hCA
  have hfinal : B*((B-ell*(w+1))*K)≤B*(ell*(B+1)*A) := by
    nlinarith only [hleft,hright]
  exact (mul_le_mul_iff_right₀ hB).mp hfinal

theorem actual_minimal_trace_weighted (c : ℤ) (M m K ell w B : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hB : 0<B) (hK : B^2≤K)
    (hdiv : ∀ d∈I,d∣M) (htrace : ∀ d∈I,P d)
    (hminimal : ∀ d∈I,∀ e,0<e → e∣d → P e → d≤e)
    (hend : ∀ d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀ d∈I,k d<2^ell) (homega : m.primeFactors.card≤w)
    (hunion : K≤(I.biUnion (fun d => Prefix c d (k d))).card) :
    (B-ell*(w+1))*K≤ell*(B+1)*
      (∑ d∈I,(PrimePrefix35.CoprimePrefix m (k d)).card) := by
  have hsquare := TraceAntichain35.minimal_trace_index_square hM I P k hdiv htrace hminimal
    (fun d hd => endpoint_quotient_le (Nat.pos_of_dvd_of_pos (hdiv d hd) hM) (hend d hd))
  have hcover := hunion.trans (prefix_union_card c I k)
  have hs := Finset.sum_le_sum (fun d hd => PrimePrefix35.actual_prime_prefix_row_omega
    m (k d) ell w hm (hfinite d hd) homega)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hs
  apply weighted_trace_payment B ell w K I.card (∑ d∈I,k d) _ hB hsquare hcover hK
  nlinarith only [hs]

theorem dyadic_even_parameter (ell j : ℕ) (hell : 2≤ell) : ell+2*j≤2^j*ell := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs : ell+2*(j+1)≤2*(ell+2*j) := by omega
    have hh := Nat.mul_le_mul_left 2 ih
    rw [pow_succ]
    nlinarith only [hs,hh]

theorem dyadic_parameter (ell j : ℕ) (hell : 2≤ell) :
    ell+j≤2^(j/2)*(ell+1) := by
  have hh := dyadic_even_parameter (ell+1) (j/2) (by omega)
  omega

theorem dyadic_root_square (B K j : ℕ) (hBK : B^2≤K) :
    (2^(j/2)*B)^2≤2^j*K := by
  have hj : 2*(j/2)≤j := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hj
  have hb := Nat.mul_le_mul_left (2^(2*(j/2))) hBK
  have hk := Nat.mul_le_mul_right K hp
  have he : (2^(j/2)*B)^2=2^(2*(j/2))*B^2 := by
    rw [mul_pow,←pow_mul]
    congr 2
    omega
  rw [he]
  exact hb.trans hk

theorem dyadic_reciprocal_block (a : ℕ) (ha : 0<a) :
    (∑ i∈Finset.Ico a (a+a),(1:ℝ)/i)≤1 := by
  have hsum : (∑ i∈Finset.Ico a (a+a),(1:ℝ)/i)≤
      ∑ _i∈Finset.Ico a (a+a),(1:ℝ)/a := by
    apply Finset.sum_le_sum
    intro i hi
    exact one_div_le_one_div_of_le (by exact_mod_cast ha) (by
      exact_mod_cast (Finset.mem_Ico.mp hi).1)
  have hr : (a:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt ha)
  simpa only [Finset.sum_const,Nat.card_Ico,Nat.add_sub_cancel_left,
    nsmul_eq_mul,mul_one_div_cancel hr] using hsum

theorem reciprocal_prefix_pow_two (J : ℕ) :
    (∑ i∈Finset.Ico (1:ℕ) (2^J),(1:ℝ)/i)≤J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hp : 0<(2:ℕ)^J := by positivity
    have he : (2:ℕ)^(J+1)=2^J+2^J := by rw [pow_succ]; omega
    rw [he,←Finset.sum_Ico_consecutive (fun i : ℕ => (1:ℝ)/i)
      (by omega : 1≤2^J) (by omega : 2^J≤2^J+2^J)]
    have hb := dyadic_reciprocal_block (2^J) hp
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

theorem actual_harmonic_le_dyadic (N J : ℕ) (hN : N<2^J) :
    HarmonicAbel29.Harmonic N≤J := by
  have hsub : Finset.Icc 1 N⊆Finset.Ico (1:ℕ) (2^J) := by
    intro i hi
    obtain ⟨hil,hiN⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Ico.mpr ⟨hil,hiN.trans_lt hN⟩
  have hs : HarmonicAbel29.Harmonic N≤∑ i∈Finset.Ico (1:ℕ) (2^J),(1:ℝ)/i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  exact hs.trans (reciprocal_prefix_pow_two J)

#print axioms weighted_trace_payment
#print axioms actual_minimal_trace_weighted
#print axioms dyadic_even_parameter
#print axioms dyadic_parameter
#print axioms dyadic_root_square
#print axioms dyadic_reciprocal_block
#print axioms reciprocal_prefix_pow_two
#print axioms actual_harmonic_le_dyadic
end
end JSP233.ShortPayment37
