import Erdos272.Arithmetic.HarmonicDiv121
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Uniform first and second logarithmic kernels. Every small quotient is
covered by finite ordinary-Lean Taylor bounds, with no numerical oracle. -/
namespace JSP233.LogKernel122
open HarmonicAbel29 HarmonicLog55 HarmonicDiv121 SimplexMoment57
open scoped Classical BigOperators
open MeasureTheory Set intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def J (n : ℕ) : ℕ :=
  if n≤1 then 0 else if n≤2 then 1 else if n≤4 then 2 else if n≤8 then 3 else 4

def X (n : ℕ) : ℝ := 1-(n:ℝ)/(2:ℝ)^(J n)
def Taylor (n : ℕ) : ℝ := ∑i∈Finset.range 6,(X n)^(i+1)/(i+1:ℕ)
def Error (n : ℕ) : ℝ := (X n)^7/(1-X n)
def Lower (n : ℕ) : ℝ := (J n:ℝ)*(149337754816/215448838605)-Taylor n-Error n
def Upper (n : ℕ) : ℝ := (J n:ℝ)*(173287/250000)-Taylor n+Error n

def Lo (n : ℕ) : ℝ :=
  (match n with
  | 1 => 0
  | 2 => 693147
  | 3 => 1098542
  | 4 => 1386294
  | 5 => 1607991
  | 6 => 1791689
  | 7 => 1945909
  | 8 => 2079441
  | 9 => 2192484
  | 10 => 2301139
  | 11 => 2397529
  | 12 => 2484836
  | 13 => 2564940
  | 14 => 2639056
  | 15 => 2708050
  | 16 => 2772588
  | _ => 0)/1000000

def Hi (n : ℕ) : ℝ :=
  (match n with
  | 1 => 0
  | 2 => 693148
  | 3 => 1098707
  | 4 => 1386296
  | 5 => 1611332
  | 6 => 1791855
  | 7 => 1945914
  | 8 => 2079444
  | 9 => 2203397
  | 10 => 2304480
  | 11 => 2398380
  | 12 => 2485003
  | 13 => 2564965
  | 14 => 2639062
  | 15 => 2708054
  | 16 => 2772592
  | _ => 0)/1000000

theorem taylor_bounds16 {n : ℕ} (hn : n∈Finset.Icc (1:ℕ) 16) :
    Lower n≤Real.log n ∧ Real.log n≤Upper n := by
  obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
  have hj : n≤2^(J n) := by interval_cases n <;> norm_num [J]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hp : (0:ℝ)<(2:ℝ)^(J n) := by positivity
  have hjR : (n:ℝ)≤(2:ℝ)^(J n) := by exact_mod_cast hj
  have hx0 : 0≤X n := by dsimp only [X];exact sub_nonneg.mpr ((div_le_one hp).mpr hjR)
  have hx1 : X n<1 := by dsimp only [X];have hh := div_pos hnR hp;linarith only [hh]
  have h := Real.abs_log_sub_add_sum_range_le (x:=X n) (by rw [abs_of_nonneg hx0];exact hx1) 6
  rw [abs_of_nonneg hx0] at h
  replace h : |Taylor n+Real.log (1-X n)|≤Error n := by
    simpa only [Taylor,Error,Nat.cast_add,Nat.cast_one,Nat.reduceAdd] using h
  have he : (1:ℝ)-X n=(n:ℝ)/(2:ℝ)^(J n) := by dsimp only [X];ring
  rw [he,Real.log_div hnR.ne' hp.ne',Real.log_pow] at h
  have hl := mul_le_mul_of_nonneg_left actual_log_two_lower (Nat.cast_nonneg (J n): (0:ℝ)≤J n)
  have hu := mul_le_mul_of_nonneg_left actual_log_two_upper (Nat.cast_nonneg (J n): (0:ℝ)≤J n)
  constructor
  · dsimp only [Lower];linarith only [(abs_le.mp h).1,hl]
  · dsimp only [Upper];linarith only [(abs_le.mp h).2,hu]

theorem rounded_bounds16 {n : ℕ} (hn : n∈Finset.Icc (1:ℕ) 16) :
    Lo n≤Real.log n ∧ Real.log n≤Hi n := by
  have h := taylor_bounds16 hn
  have hr : Lo n≤Lower n ∧ Upper n≤Hi n := by
    obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> norm_num [Lo,Hi,Lower,Upper,Taylor,Error,X,J,Finset.sum_range_succ]
  exact ⟨hr.1.trans h.1,h.2.trans hr.2⟩

theorem lo_nonnegative16 {n : ℕ} (hn : n∈Finset.Icc (1:ℕ) 16) : 0≤Lo n := by
  obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
  interval_cases n <;> norm_num [Lo]

theorem small_kernel_rational1 {n : ℕ} (hn : n∈Finset.Icc (1:ℕ) 16) :
    (∑d∈Finset.Icc (1:ℕ) n,(Hi n-Lo d)/(d:ℝ))≤
      (Lo n)^2/2+(61/100:ℝ)*Lo n+1/20 := by
  obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
  interval_cases n <;> norm_num [Lo,Hi,Finset.sum_Icc_succ_top]

theorem small_kernel_rational2 {n : ℕ} (hn : n∈Finset.Icc (1:ℕ) 16) :
    (∑d∈Finset.Icc (1:ℕ) n,(Hi n-Lo d)^2/(d:ℝ))≤
      (Lo n)^3/3+(61/100:ℝ)*(Lo n)^2+1/4 := by
  obtain ⟨hn,h16⟩ := Finset.mem_Icc.mp hn
  interval_cases n <;> norm_num [Lo,Hi,Finset.sum_Icc_succ_top]

theorem actual_small_kernel_sum (k : ℕ) {N : ℕ} (hN : N∈Finset.Icc (1:ℕ) 16) :
    (∑d∈Finset.Icc (1:ℕ) N,LogKernel N k d)≤
      ∑d∈Finset.Icc (1:ℕ) N,(Hi N-Lo d)^k/(d:ℝ) := by
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨hd0,hdN⟩ := Finset.mem_Icc.mp hd
  have hd16 : d∈Finset.Icc (1:ℕ) 16 := Finset.mem_Icc.mpr ⟨hd0,hdN.trans (Finset.mem_Icc.mp hN).2⟩
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr (Finset.mem_Icc.mp hN).1
  have hdpos : (0:ℝ)<d := Nat.cast_pos.mpr hd0
  have hl := Real.log_le_log hdpos (show (d:ℝ)≤N by exact_mod_cast hdN)
  have hb : Real.log N-Real.log d≤Hi N-Lo d := by
    linarith only [(rounded_bounds16 hN).2,(rounded_bounds16 hd16).1]
  dsimp only [LogKernel]
  apply div_le_div_of_nonneg_right _ hdpos.le
  exact pow_le_pow_left₀ (sub_nonneg.mpr hl) hb k

theorem actual_prefix_second_log16 :
    (∑d∈Finset.Icc (1:ℕ) 16,(Real.log (d:ℝ))^2/(d:ℝ))≤
      (Real.log (16:ℝ))^3/3+1/4 := by
  have hs : (∑d∈Finset.Icc (1:ℕ) 16,(Real.log (d:ℝ))^2/(d:ℝ))≤
      ∑d∈Finset.Icc (1:ℕ) 16,(Hi d)^2/(d:ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hl0 : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
    have hb := (rounded_bounds16 hd).2
    gcongr
  have hr : (∑d∈Finset.Icc (1:ℕ) 16,(Hi d)^2/(d:ℝ))≤(Lo 16)^3/3+1/4 := by
    norm_num [Hi,Lo,Finset.sum_Icc_succ_top]
  have hl := (rounded_bounds16 (n:=16) (by decide)).1
  norm_num only [Nat.cast_ofNat] at hl
  have hp : (Lo 16)^3≤(Real.log (16:ℝ))^3 := by
    have h0 : 0≤Lo 16 := lo_nonnegative16 (by decide)
    gcongr
  linarith only [hs,hr,hp]

theorem log_kernel_second_interval {M N : ℕ} (hM : 1≤M) (hMN : M≤N) :
    (∫t in (M:ℝ)..N,LogKernel N 2 t)=(Real.log N-Real.log M)^3/3 := by
  have hMN' : (M:ℝ)≤N := by exact_mod_cast hMN
  have hNR : (1:ℝ)≤N := by exact_mod_cast (hM.trans hMN)
  have hder : ∀t∈uIcc (M:ℝ) N,
      HasDerivAt (fun t:ℝ=>-((Real.log N-Real.log t)^3/3)) (LogKernel N 2 t) t := by
    intro t ht
    rw [uIcc_of_le hMN'] at ht
    have ht0 : t≠0 := by
      have hm : (1:ℝ)≤M := by exact_mod_cast hM
      linarith only [ht.1,hm]
    have hd := ((((Real.hasDerivAt_log ht0).const_sub (Real.log N)).pow 3).div_const 3).neg
    convert hd using 1 <;> first | rfl | (simp only [LogKernel];field_simp;ring)
  have hi : IntervalIntegrable (LogKernel N 2) volume (M:ℝ) N :=
    ((log_kernel_continuous hNR 2).mono (by
      intro x hx
      have hm : (1:ℝ)≤M := by exact_mod_cast hM
      exact ⟨hm.trans hx.1,hx.2⟩)).intervalIntegrable_of_Icc hMN'
  have hh := integral_eq_sub_of_hasDerivAt hder hi
  simpa only [sub_self,zero_pow (by decide : 3≠0),zero_div,neg_zero,zero_sub,neg_neg] using hh

theorem actual_large_kernel_sum2 {N : ℕ} (hN : 16≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 2 d)≤
      (Real.log N)^3/3+(61/100:ℝ)*(Real.log N)^2+1/4 := by
  have hNR : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have haf : AntitoneOn (LogKernel (N:ℝ) 2) (Icc ((16:ℕ):ℝ) (N:ℝ)) :=
    (log_kernel_antitone hNR 2).mono (by intro x hx;norm_num only [Nat.cast_ofNat] at hx;exact ⟨by linarith only [hx.1],hx.2⟩)
  have hi := AntitoneOn.sum_le_integral_Ico hN haf
  have hshift : (∑a∈Finset.Ico 16 N,LogKernel (N:ℝ) 2 ((a+1:ℕ):ℝ))=
      ∑a∈Finset.Ico 17 (N+1),LogKernel (N:ℝ) 2 a := by
    simpa only [Nat.reduceAdd] using (Finset.sum_Ico_add' (fun a:ℕ=>LogKernel (N:ℝ) 2 a) 16 N 1)
  rw [hshift,log_kernel_second_interval (by decide : 1≤16) hN] at hi
  have hfull : (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 2 d)=
      (∑d∈Finset.Icc (1:ℕ) 16,LogKernel N 2 d)+∑d∈Finset.Ico 17 (N+1),LogKernel N 2 d := by
    rw [←Finset.Ico_add_one_right_eq_Icc,←Finset.Ico_add_one_right_eq_Icc]
    exact (Finset.sum_Ico_consecutive (fun a:ℕ=>LogKernel N 2 a) (by decide : 1≤17) (by omega : 17≤N+1)).symm
  have hp : (∑d∈Finset.Icc (1:ℕ) 16,LogKernel N 2 d)=
      (Real.log N)^2*Harmonic 16-2*Real.log N*(∑d∈Finset.Icc (1:ℕ) 16,Real.log (d:ℝ)/(d:ℝ))+
        ∑d∈Finset.Icc (1:ℕ) 16,(Real.log (d:ℝ))^2/(d:ℝ) := by
    have he : ∀d:ℕ,LogKernel N 2 d=(Real.log N)^2*(1/(d:ℝ))-
        2*Real.log N*(Real.log (d:ℝ)/(d:ℝ))+(Real.log (d:ℝ))^2/(d:ℝ) := by
      intro d;dsimp only [LogKernel];ring
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,Harmonic]
  have hh : Harmonic 16=(2436559/720720:ℝ) := by norm_num [Harmonic,Finset.sum_Icc_succ_top]
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    have he : (16:ℝ)=(2:ℝ)^4 := by norm_num
    rw [he,Real.log_pow];norm_num
  have hc : Harmonic 16-Real.log 16≤(61/100:ℝ) := by
    rw [hh,h16]
    linarith only [actual_log_two_lower]
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg hNR
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log (N:ℝ)))
  have hpre1 : (Real.log (16:ℝ))^2≤2*∑d∈Finset.Icc (1:ℕ) 16,Real.log (d:ℝ)/(d:ℝ) := by
    rw [h16]
    nlinarith only [actual_prefix_log16]
  have hfee := mul_le_mul_of_nonneg_right hpre1 hl0
  have hpre2 := actual_prefix_second_log16
  rw [hfull,hp]
  norm_num only [Nat.cast_ofNat] at hi
  nlinarith only [hi,hm,hfee,hpre2]

theorem actual_log_kernel_sum1 {N : ℕ} (hN : 1≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 1 d)≤
      (Real.log N)^2/2+(61/100:ℝ)*Real.log N+1/20 := by
  by_cases h16 : 16≤N
  · have h := actual_log_kernel61 h16
    linarith only [h]
  · have hn : N∈Finset.Icc (1:ℕ) 16 := Finset.mem_Icc.mpr ⟨hN,by omega⟩
    have hs := actual_small_kernel_sum 1 hn
    simp only [pow_one] at hs
    have hr := small_kernel_rational1 hn
    have hl := (rounded_bounds16 hn).1
    have h0 := lo_nonnegative16 hn
    have hp : (Lo N)^2≤(Real.log (N:ℝ))^2 := by gcongr
    linarith only [hs,hr,hl,hp]

theorem actual_log_kernel_sum2 {N : ℕ} (hN : 1≤N) :
    (∑d∈Finset.Icc (1:ℕ) N,LogKernel N 2 d)≤
      (Real.log N)^3/3+(61/100:ℝ)*(Real.log N)^2+1/4 := by
  by_cases h16 : 16≤N
  · exact actual_large_kernel_sum2 h16
  · have hn : N∈Finset.Icc (1:ℕ) 16 := Finset.mem_Icc.mpr ⟨hN,by omega⟩
    have hs := actual_small_kernel_sum 2 hn
    have hr := small_kernel_rational2 hn
    have hl := (rounded_bounds16 hn).1
    have h0 := lo_nonnegative16 hn
    have hp : (Lo N)^2≤(Real.log (N:ℝ))^2 := by gcongr
    have hc : (Lo N)^3≤(Real.log (N:ℝ))^3 := by gcongr
    linarith only [hs,hr,hp,hc]

#print axioms taylor_bounds16
#print axioms rounded_bounds16
#print axioms lo_nonnegative16
#print axioms small_kernel_rational1
#print axioms small_kernel_rational2
#print axioms actual_small_kernel_sum
#print axioms actual_prefix_second_log16
#print axioms log_kernel_second_interval
#print axioms actual_large_kernel_sum2
#print axioms actual_log_kernel_sum1
#print axioms actual_log_kernel_sum2
end
end JSP233.LogKernel122
