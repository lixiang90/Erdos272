import Erdos272.Arithmetic.LogKernel122

/-! The actual divisor recursion with corrected first and second logarithmic
kernels. Every physical floor quotient, including1, is retained. The actual
gcd-factor encoding pays the divisor second moment without a supplied budget. -/
namespace JSP233.DivisorMoment122
open SimplexMoment57 HarmonicAbel29 DivisorMoment45
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Q2 (L : ℝ) : ℝ := L^2/2+(121/100)*L+27/25
def Q3 (L : ℝ) : ℝ := L^3/6+(91/100)*L^2+(18181/10000)*L+2531/2000

theorem q2_nonnegative {L : ℝ} (hL : 0≤L) : 0≤Q2 L := by
  dsimp only [Q2]
  positivity

theorem q3_nonnegative {L : ℝ} (hL : 0≤L) : 0≤Q3 L := by
  dsimp only [Q3]
  positivity

theorem q3_monotone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : Q3 x≤Q3 y := by
  dsimp only [Q3]
  gcongr

theorem div_count_one_corrected {N : ℕ} (hN : 1≤N) :
    (DivCount 1 N:ℝ)≤(N:ℝ)*(Real.log N+3/5)+43/100 := by
  have hn0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  calc
    _≤(N:ℝ)*Harmonic N := div_count_one_harmonic N
    _≤(N:ℝ)*(Real.log N+3/5+43/(100*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left (HarmonicDiv121.actual_harmonic43 hN) (Nat.cast_nonneg N)
    _=_ := by field_simp [hn0]

theorem div_count_two_prefix {N : ℕ} (hN : 1≤N) :
    (DivCount 2 N:ℝ)≤(N:ℝ)*Q2 (Real.log N) := by
  have hs0 := actual_log_kernel_sum hN 0
  have hs1 := LogKernel122.actual_log_kernel_sum1 hN
  norm_num at hs0
  have heq : (DivCount 2 N:ℝ)=∑a∈Finset.Icc 1 N,(DivCount 1 (N/a):ℝ) := by
    simp only [DivCount,Nat.cast_sum]
  rw [heq]
  calc
    _≤∑a∈Finset.Icc 1 N,(((N:ℝ)/a)*(Real.log N-Real.log a+3/5)+43/100) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hn,hcast,_h0,hl,_hL⟩ := actual_quotient_log_bounds ha
      have hp : Real.log ((N/a:ℕ):ℝ)+3/5≤Real.log N-Real.log a+3/5 := by
        linarith only [hl]
      exact (div_count_one_corrected hn).trans
        (add_le_add (mul_le_mul hcast hp (by positivity) (by positivity)) (le_refl (43/100:ℝ)))
    _=(N:ℝ)*((3/5)*(∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 0 a)+
        ∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 1 a)+(43/100)*N := by
      have hsum : (∑a∈Finset.Icc 1 N,(((N:ℝ)/a)*(Real.log N-Real.log a+3/5)+43/100))=
          ∑a∈Finset.Icc 1 N,((3/5*N)*LogKernel (N:ℝ) 0 a+N*LogKernel (N:ℝ) 1 a+43/100) := by
        apply Finset.sum_congr rfl
        intro a _ha
        dsimp only [LogKernel]
        ring
      rw [hsum,Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
      ring
    _≤(N:ℝ)*((3/5)*(1+Real.log N)+((Real.log N)^2/2+(61/100)*Real.log N+1/20))+(43/100)*N :=
      add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hs0 (by norm_num)) hs1) (Nat.cast_nonneg N))
        (le_refl ((43/100:ℝ)*N))
    _=(N:ℝ)*Q2 (Real.log N) := by dsimp only [Q2];ring

theorem div_count_three_prefix {N : ℕ} (hN : 1≤N) :
    (DivCount 3 N:ℝ)≤(N:ℝ)*Q3 (Real.log N) := by
  have hs0 := actual_log_kernel_sum hN 0
  have hs1 := LogKernel122.actual_log_kernel_sum1 hN
  have hs2 := LogKernel122.actual_log_kernel_sum2 hN
  norm_num at hs0
  have heq : (DivCount 3 N:ℝ)=∑a∈Finset.Icc 1 N,(DivCount 2 (N/a):ℝ) := by
    simp only [DivCount,Nat.cast_sum]
  rw [heq]
  calc
    _≤∑a∈Finset.Icc 1 N,((N:ℝ)/a)*Q2 (Real.log N-Real.log a) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hn,hcast,h0,hl,_hL⟩ := actual_quotient_log_bounds ha
      have hp : Q2 (Real.log ((N/a:ℕ):ℝ))≤Q2 (Real.log N-Real.log a) := by
        dsimp only [Q2]
        gcongr
      exact (div_count_two_prefix hn).trans
        (mul_le_mul hcast hp (q2_nonnegative h0) (by positivity))
    _=(N:ℝ)*((27/25)*(∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 0 a)+
        (121/100)*(∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 1 a)+
        (∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 2 a)/2) := by
      have hsum : (∑a∈Finset.Icc 1 N,((N:ℝ)/a)*Q2 (Real.log N-Real.log a))=
          ∑a∈Finset.Icc 1 N,((27/25*N)*LogKernel (N:ℝ) 0 a+
            (121/100*N)*LogKernel (N:ℝ) 1 a+(N/2)*LogKernel (N:ℝ) 2 a) := by
        apply Finset.sum_congr rfl
        intro a _ha
        dsimp only [Q2,LogKernel]
        ring
      rw [hsum,Finset.sum_add_distrib,Finset.sum_add_distrib,
        ←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]
      ring
    _≤(N:ℝ)*((27/25)*(1+Real.log N)+
        (121/100)*((Real.log N)^2/2+(61/100)*Real.log N+1/20)+
        ((Real.log N)^3/3+(61/100)*(Real.log N)^2+1/4)/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hs0 (by norm_num))
          (mul_le_mul_of_nonneg_left hs1 (by norm_num)))
        (div_le_div_of_nonneg_right hs2 (by norm_num))
    _=(N:ℝ)*Q3 (Real.log N) := by dsimp only [Q3];ring

theorem actual_divisor_second_moment_prefix {N : ℕ} (hN : 1≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤(N:ℝ)*Q3 (Real.log N) := by
  have hh : ((∑n∈Finset.Icc 1 N,n.divisors.card^2:ℕ):ℝ)≤(QuadPool N).card := by
    exact_mod_cast actual_second_moment_encoding N
  rw [quad_pool_eq_div_count] at hh
  simpa only [Nat.cast_sum,Nat.cast_pow] using hh.trans (div_count_three_prefix hN)

#print axioms q2_nonnegative
#print axioms q3_nonnegative
#print axioms q3_monotone
#print axioms div_count_one_corrected
#print axioms div_count_two_prefix
#print axioms div_count_three_prefix
#print axioms actual_divisor_second_moment_prefix
end
end JSP233.DivisorMoment122
