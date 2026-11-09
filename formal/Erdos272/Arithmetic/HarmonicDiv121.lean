module

public import Erdos272.Resources.LocalMobius119
public import Erdos272.Arithmetic.HarmonicCorrect118
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Finite-prefix logarithmic summation and a uniform corrected harmonic
bound. All quotient lengths, including1, remain in the physical sum. -/
namespace JSP233.HarmonicDiv121
open HarmonicAbel29 HarmonicLog55 HarmonicCorrect118 SimplexMoment57
open scoped Classical BigOperators
open MeasureTheory Set intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem dyadic_log_lower (n j : ℕ) (hn : 0<n) (hj : 2^j≤n) :
    (j:ℝ)*Real.log 2+2*((n:ℝ)-(2:ℝ)^j)/((n:ℝ)+(2:ℝ)^j)≤Real.log n := by
  have hp : (0:ℝ)<(2:ℝ)^j := by positivity
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hjR : (2:ℝ)^j≤n := by exact_mod_cast hj
  have h := Real.le_log_one_add_of_nonneg (div_nonneg (sub_nonneg.mpr hjR) hp.le)
  have he : (1:ℝ)+((n:ℝ)-(2:ℝ)^j)/(2:ℝ)^j=(n:ℝ)/(2:ℝ)^j := by field_simp;ring
  rw [he,Real.log_div hnR.ne' hp.ne',Real.log_pow] at h
  have hr : 2*(((n:ℝ)-(2:ℝ)^j)/(2:ℝ)^j)/
      ((((n:ℝ)-(2:ℝ)^j)/(2:ℝ)^j)+2)=2*((n:ℝ)-(2:ℝ)^j)/((n:ℝ)+(2:ℝ)^j) := by
    have he2 : (((n:ℝ)-(2:ℝ)^j)/(2:ℝ)^j)+2=((n:ℝ)+(2:ℝ)^j)/(2:ℝ)^j := by field_simp;ring
    rw [he2]
    field_simp [hp.ne',(add_pos hnR hp).ne']
  rw [hr] at h
  linarith only [h]

theorem harmonic43_step {n : ℕ} (hn : 4≤n) :
    Harmonic (n+1)-Real.log (n+1)-43/(100*((n:ℝ)+1))≤
      Harmonic n-Real.log n-43/(100*(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn4 : (4:ℝ)≤n := by exact_mod_cast hn
  have hlog := Real.le_log_one_add_of_nonneg (show (0:ℝ)≤1/(n:ℝ) by positivity)
  have he : (1:ℝ)+1/(n:ℝ)=((n:ℝ)+1)/(n:ℝ) := by field_simp
  rw [he,Real.log_div (by positivity) hnR.ne'] at hlog
  have hr : (1:ℝ)/((n:ℝ)+1)+43/(100*(n:ℝ))-43/(100*((n:ℝ)+1))≤
      2*(1/(n:ℝ))/(1/(n:ℝ)+2) := by
    have hd : (1:ℝ)/(n:ℝ)+2=(2*(n:ℝ)+1)/(n:ℝ) := by field_simp;ring
    rw [hd]
    field_simp
    nlinarith only [hn4]
  rw [harmonic_successor]
  linarith only [hlog,hr]

theorem actual_harmonic43 {n : ℕ} (hn : 1≤n) :
    Harmonic n≤Real.log n+3/5+43/(100*(n:ℝ)) := by
  by_cases h4 : 4≤n
  · have hm : Harmonic n-Real.log n-43/(100*(n:ℝ))≤
        Harmonic 4-Real.log 4-43/400 := by
      clear hn
      induction n,h4 using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        have hs := harmonic43_step hk
        simpa only [Nat.cast_add,Nat.cast_one] using hs.trans ih
    have hb := dyadic_log_lower 4 2 (by decide) (by decide)
    norm_num only [Nat.cast_ofNat] at hb
    have hh : Harmonic 4=(25/12:ℝ) := by norm_num [Harmonic,Finset.sum_Icc_succ_top]
    have hl := actual_log_two_lower
    rw [hh] at hm
    nlinarith only [hm,hb,hl]
  · rcases (show n=1 ∨ n=2 ∨ n=3 by omega) with h | h | h <;> subst n
    · norm_num [Harmonic,Finset.sum_Icc_succ_top]
    · have hl := actual_log_two_lower
      norm_num [Harmonic,Finset.sum_Icc_succ_top]
      linarith only [hl]
    · have hl := dyadic_log_lower 3 1 (by decide) (by decide)
      have hb := actual_log_two_lower
      norm_num [Harmonic,Finset.sum_Icc_succ_top] at *
      linarith only [hl,hb]

def PrefixLower (n : ℕ) : ℝ :=
  let j := if n<2 then 0 else if n<4 then 1 else if n<8 then 2 else if n<16 then 3 else 4
  (j:ℝ)*Real.log 2+2*((n:ℝ)-(2:ℝ)^j)/((n:ℝ)+(2:ℝ)^j)

theorem prefix_lower (n : ℕ) (hn : n∈Finset.Icc (1:ℕ) 16) : PrefixLower n≤Real.log n := by
  obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
  interval_cases n
  · norm_num [PrefixLower]
  · norm_num [PrefixLower]
  · simpa [PrefixLower] using dyadic_log_lower 3 1 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 4 2 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 5 2 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 6 2 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 7 2 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 8 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 9 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 10 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 11 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 12 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 13 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 14 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 15 3 (by decide) (by decide)
  · simpa [PrefixLower] using dyadic_log_lower 16 4 (by decide) (by decide)

theorem actual_prefix_log16 :
    8*(Real.log 2)^2≤∑n∈Finset.Icc (1:ℕ) 16,Real.log (n:ℝ)/(n:ℝ) := by
  have hs := Finset.sum_le_sum (fun n hn=>
    div_le_div_of_nonneg_right (prefix_lower n hn) (Nat.cast_nonneg (α:=ℝ) n))
  have he : (∑n∈Finset.Icc (1:ℕ) 16,PrefixLower n/(n:ℝ))=
      (27333/5720:ℝ)*Real.log 2+71729653/133855722 := by
    norm_num [PrefixLower,Finset.sum_Icc_succ_top]
    ring
  rw [he] at hs
  have hl := actual_log_two_lower
  have hu := actual_log_two_upper
  have hsq : (Real.log 2)^2≤(173287/250000:ℝ)^2 := by
    have hz : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    gcongr
  nlinarith only [hs,hl,hsq]

theorem log_kernel_interval {M N : ℕ} (hM : 1≤M) (hMN : M≤N) :
    (∫t in (M:ℝ)..N,LogKernel N 1 t)=(Real.log N-Real.log M)^2/2 := by
  have hMN' : (M:ℝ)≤N := by exact_mod_cast hMN
  have hNR : (1:ℝ)≤N := by exact_mod_cast (hM.trans hMN)
  have hder : ∀t∈uIcc (M:ℝ) N,
      HasDerivAt (fun t:ℝ=>-((Real.log N-Real.log t)^2/2))
        (LogKernel N 1 t) t := by
    intro t ht
    rw [uIcc_of_le hMN'] at ht
    have ht0 : t≠0 := by
      have hm : (1:ℝ)≤M := by exact_mod_cast hM
      linarith only [ht.1,hm]
    have hd := ((((Real.hasDerivAt_log ht0).const_sub (Real.log N)).pow 2).div_const 2).neg
    convert hd using 1 <;> first | rfl | (simp only [LogKernel,pow_one];field_simp;ring)
  have hi : IntervalIntegrable (LogKernel N 1) volume (M:ℝ) N :=
    ((log_kernel_continuous hNR 1).mono (by
      intro x hx
      have hm : (1:ℝ)≤M := by exact_mod_cast hM
      exact ⟨hm.trans hx.1,hx.2⟩)).intervalIntegrable_of_Icc hMN'
  have hh := integral_eq_sub_of_hasDerivAt hder hi
  simpa only [sub_self,zero_pow (by decide : 2≠0),zero_div,neg_zero,zero_sub,neg_neg] using hh

theorem actual_log_kernel61 {N : ℕ} (hN : 16≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 1 d)≤(Real.log N)^2/2+(61/100:ℝ)*Real.log N := by
  have hNR : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have haf : AntitoneOn (LogKernel (N:ℝ) 1) (Icc ((16:ℕ):ℝ) (N:ℝ)) :=
    (log_kernel_antitone hNR 1).mono (by intro x hx;norm_num only [Nat.cast_ofNat] at hx;exact ⟨by linarith only [hx.1],hx.2⟩)
  have hi := AntitoneOn.sum_le_integral_Ico hN haf
  have hshift : (∑a∈Finset.Ico 16 N,LogKernel (N:ℝ) 1 ((a+1:ℕ):ℝ))=
      ∑a∈Finset.Ico 17 (N+1),LogKernel (N:ℝ) 1 a := by
    simpa only [Nat.reduceAdd] using (Finset.sum_Ico_add' (fun a:ℕ=>LogKernel (N:ℝ) 1 a) 16 N 1)
  rw [hshift,log_kernel_interval (by decide : 1≤16) hN] at hi
  have hfull : (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 1 d)=
      (∑d∈Finset.Icc (1:ℕ) 16,LogKernel N 1 d)+∑d∈Finset.Ico 17 (N+1),LogKernel N 1 d := by
    rw [←Finset.Ico_add_one_right_eq_Icc,←Finset.Ico_add_one_right_eq_Icc]
    exact (Finset.sum_Ico_consecutive (fun a:ℕ=>LogKernel N 1 a) (by decide : 1≤17) (by omega : 17≤N+1)).symm
  have hp : (∑d∈Finset.Icc (1:ℕ) 16,LogKernel N 1 d)=
      Real.log N*Harmonic 16-∑d∈Finset.Icc (1:ℕ) 16,Real.log (d:ℝ)/(d:ℝ) := by
    simp only [LogKernel,pow_one,sub_div,Finset.sum_sub_distrib,Harmonic,mul_one_div,Finset.mul_sum]
  have hh : Harmonic 16=(2436559/720720:ℝ) := by norm_num [Harmonic,Finset.sum_Icc_succ_top]
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    have he : (16:ℝ)=(2:ℝ)^4 := by norm_num
    rw [he,Real.log_pow];norm_num
  have hc : Harmonic 16-Real.log 16≤(61/100:ℝ) := by
    rw [hh,h16]
    linarith only [actual_log_two_lower]
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg hNR
  have hm := mul_le_mul_of_nonneg_right hc hl0
  rw [hfull,hp]
  norm_num only [Nat.cast_ofNat] at hi
  rw [h16] at hi hm
  nlinarith only [hi,hm,actual_prefix_log16]

theorem actual_quotient_reciprocal_sum {N : ℕ} (hN : 1≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,1/((d:ℝ)*(N/d:ℕ)))≤2 := by
  have hnR : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hs : ∀d∈Finset.Icc (1:ℕ) N,1/((d:ℝ)*(N/d:ℕ))≤2/(N:ℝ) := by
    intro d hd
    obtain ⟨hd,hdN⟩ := Finset.mem_Icc.mp hd
    have hq : 1≤N/d := Nat.div_pos hdN hd
    have hrem := Nat.mod_lt N hd
    have hdecomp := Nat.div_add_mod N d
    have hmul : N≤2*(d*(N/d)) := by nlinarith only [hdecomp,hrem,hq]
    have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
    have hqR : (0:ℝ)<(N/d:ℕ) := Nat.cast_pos.mpr hq
    apply (div_le_div_iff₀ (mul_pos hdR hqR) hnR).mpr
    norm_num only [one_mul]
    exact_mod_cast hmul
  have hh := Finset.sum_le_sum hs
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hh
  have he : (N:ℝ)*(2/(N:ℝ))=2 := by field_simp
  rw [he] at hh
  exact hh

theorem actual_harmonic_div_sum61 {N : ℕ} (hN : 16≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,Harmonic (N/d)/(d:ℝ))≤
      (Real.log N)^2/2+(61/100:ℝ)*Real.log N+(3/5:ℝ)*Harmonic N+43/50 := by
  have hs : (∑d∈Finset.Icc (1:ℕ) N,Harmonic (N/d)/(d:ℝ))≤
      ∑d∈Finset.Icc (1:ℕ) N,(LogKernel N 1 d+(3/5:ℝ)/d+43/100*(1/((d:ℝ)*(N/d:ℕ)))) := by
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hd,hNd⟩ := Finset.mem_Icc.mp hd
    have hq := Nat.div_pos hNd hd
    have hb := actual_harmonic43 hq
    have hl := (actual_quotient_log_bounds (Finset.mem_Icc.mpr ⟨hd,hNd⟩)).2.2.2.1
    have hh := div_le_div_of_nonneg_right (show Harmonic (N/d)≤Real.log N-Real.log d+3/5+43/(100*(N/d:ℕ)) by linarith only [hb,hl])
      (Nat.cast_nonneg (α:=ℝ) d)
    dsimp only [LogKernel]
    norm_num only [pow_one]
    convert hh using 1; ring
  have he : (∑d∈Finset.Icc (1:ℕ) N,(LogKernel N 1 d+(3/5:ℝ)/d+43/100*(1/((d:ℝ)*(N/d:ℕ)))))=
      (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 1 d)+(3/5:ℝ)*Harmonic N+
        43/100*(∑d∈Finset.Icc (1:ℕ) N,1/((d:ℝ)*(N/d:ℕ))) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,Harmonic,mul_one_div]
  rw [he] at hs
  have hk := actual_log_kernel61 hN
  have hr := actual_quotient_reciprocal_sum (by omega : 1≤N)
  linarith only [hs,hk,hr]

#print axioms dyadic_log_lower
#print axioms harmonic43_step
#print axioms actual_harmonic43
#print axioms prefix_lower
#print axioms actual_prefix_log16
#print axioms log_kernel_interval
#print axioms actual_log_kernel61
#print axioms actual_quotient_reciprocal_sum
#print axioms actual_harmonic_div_sum61
end
end JSP233.HarmonicDiv121
