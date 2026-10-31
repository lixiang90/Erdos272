import Erdos272.Arithmetic.HarmonicLog55

/-! A finite correction to the decreasing harmonic logarithmic sequence.
The 63-term exact anchor pays the full error; no asymptotic numerical
value or external Euler constant estimate is assumed. -/
namespace JSP233.HarmonicCorrect118
open HarmonicAbel29 HarmonicLog55
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem harmonic_successor (n : ℕ) : Harmonic (n+1)=Harmonic n+1/((n:ℝ)+1) := by
  unfold Harmonic
  rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
  simp only [Nat.cast_add,Nat.cast_one]

theorem corrected_harmonic_step {n : ℕ} (hn : 1≤n) :
    Harmonic (n+1)-Real.log (n+1)-1/(2*((n:ℝ)+2))≤
      Harmonic n-Real.log n-1/(2*((n:ℝ)+1)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog := Real.le_log_one_add_of_nonneg (show (0:ℝ)≤1/(n:ℝ) by positivity)
  have he : (1:ℝ)+1/(n:ℝ)=((n:ℝ)+1)/(n:ℝ) := by field_simp
  rw [he,Real.log_div (by positivity) hnR.ne'] at hlog
  have hr : (1:ℝ)/((n:ℝ)+1)+1/(2*((n:ℝ)+1))-1/(2*((n:ℝ)+2))≤
      2*(1/(n:ℝ))/(1/(n:ℝ)+2) := by
    have hn0 : (n:ℝ)≠0 := ne_of_gt hnR
    have hp1 : (0:ℝ)<(n:ℝ)+1 := by positivity
    have hp2 : (0:ℝ)<(n:ℝ)+2 := by positivity
    have hp3 : (0:ℝ)<2*(n:ℝ)+1 := by positivity
    have hd : (1:ℝ)/(n:ℝ)+2=(2*(n:ℝ)+1)/(n:ℝ) := by field_simp;ring
    rw [hd]
    field_simp
    nlinarith only [hnR]
  rw [harmonic_successor]
  linarith only [hlog,hr]

theorem corrected_harmonic_mono {M N : ℕ} (hM : 1≤M) (hMN : M≤N) :
    Harmonic N-Real.log N-1/(2*((N:ℝ)+1))≤
      Harmonic M-Real.log M-1/(2*((M:ℝ)+1)) := by
  induction N, hMN using Nat.le_induction with
  | base => exact le_rfl
  | succ n hMn ih =>
    have hs := corrected_harmonic_step (hM.trans hMn)
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hs.trans ih

theorem actual_harmonic_log_5775 {N : ℕ} (hN : 100000≤N) :
    Harmonic N≤Real.log N+231/400 := by
  have hm := corrected_harmonic_mono (M:=63) (by decide) (by omega : 63≤N)
  norm_num only [Nat.cast_ofNat] at hm
  have hb : Harmonic 63-(6*(149337754816/215448838605:ℝ)-1/63)-1/128≤57745/100000 := by
    rw [actual_harmonic63]
    norm_num
  have hn : (100000:ℝ)≤N := by exact_mod_cast hN
  have ht : (1:ℝ)/(2*((N:ℝ)+1))≤1/100000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith only [hn]
  linarith only [hm,hb,ht,actual_log63_lower]

#print axioms harmonic_successor
#print axioms corrected_harmonic_step
#print axioms corrected_harmonic_mono
#print axioms actual_harmonic_log_5775
end
end JSP233.HarmonicCorrect118

