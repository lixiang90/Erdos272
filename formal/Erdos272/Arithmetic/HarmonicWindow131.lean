module

public import Erdos272.Arithmetic.HarmonicCorrect118
public import Erdos272.Arithmetic.LogThree126
public import Erdos272.Arithmetic.Trapezoid130
public import Erdos272.Arithmetic.ConvexQuotient130

@[expose] public section
namespace JSP233.HarmonicWindow131
open HarmonicAbel29 HarmonicLog55 HarmonicCorrect118
open Set MeasureTheory intervalIntegral
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem harmonic_trap_step {n:ℕ} (hn:1≤n) :
    Harmonic n-Real.log n-1/(2*(n:ℝ))≤
      Harmonic (n+1)-Real.log (n+1)-1/(2*((n:ℝ)+1)) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hle : (n:ℝ)≤(n:ℝ)+1 := by linarith
  have hconv : ConvexOn ℝ (Icc (n:ℝ) ((n:ℝ)+1)) (fun t:ℝ=>1/t) :=
    (ConvexQuotient130.quotient_convex (x:=1) (by norm_num)).subset
      (fun t ht=>lt_of_lt_of_le hn0 ht.1) (convex_Icc _ _)
  have hc : ContinuousOn (fun t:ℝ=>1/t) (Icc (n:ℝ) ((n:ℝ)+1)) := by
    intro t ht
    exact (continuousAt_const.div continuousAt_id (ne_of_gt (lt_of_lt_of_le hn0 ht.1))).continuousWithinAt
  have hi := Trapezoid130.integral_trapezoid hle hc hconv
  rw [integral_one_div_of_pos hn0 (by positivity),Real.log_div (by positivity) hn0.ne'] at hi
  rw [harmonic_successor]
  simp only [add_sub_cancel_left,one_mul] at hi ⊢
  simp only [one_div,mul_inv_rev] at hi ⊢
  linarith only [hi]

theorem harmonic_trap_mono {m n:ℕ} (hm:1≤m) (hmn:m≤n) :
    Harmonic m-Real.log m-1/(2*(m:ℝ))≤Harmonic n-Real.log n-1/(2*(n:ℝ)) := by
  induction n,hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
    have hs := harmonic_trap_step (hm.trans hmn)
    norm_num only [Nat.cast_add,Nat.cast_one] at hs ⊢
    exact ih.trans hs

theorem log63_upper : Real.log (63:ℝ)≤6*LogThree126.TwoHi-1/64 := by
  have h64 : Real.log (64:ℝ)=6*Real.log 2 := by
    rw [show (64:ℝ)=(2:ℝ)^6 by norm_num,Real.log_pow]
    norm_num
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<63/64)
  rw [Real.log_div (by norm_num) (by norm_num),h64] at hl
  have h2 := LogThree126.log_two_window.2
  linarith only [hl,h2]

theorem corrected63_lower : (577/1000:ℝ)≤Harmonic 63-Real.log 63-1/126 := by
  have hb : (577/1000:ℝ)≤Harmonic 63-(6*LogThree126.TwoHi-1/64)-1/126 := by
    rw [actual_harmonic63]
    norm_num [LogThree126.TwoHi]
  linarith only [hb,log63_upper]

theorem corrected63_upper : Harmonic 63-Real.log 63-1/128≤(57745/100000:ℝ) := by
  have hb : Harmonic 63-(6*(149337754816/215448838605:ℝ)-1/63)-1/128≤57745/100000 := by
    rw [actual_harmonic63]
    norm_num
  linarith only [hb,actual_log63_lower]

theorem harmonic_lower {n:ℕ} (hn:1≤n) : Real.log n+577/1000≤Harmonic n := by
  by_cases h63:63≤n
  · have hm := harmonic_trap_mono (m:=63) (by decide) h63
    norm_num only [Nat.cast_ofNat] at hm
    have hp : (0:ℝ)≤1/(2*(n:ℝ)) := by positivity
    linarith only [hm,corrected63_lower,hp]
  · have hm := actual_harmonic_log_mono hn (by omega : n≤63)
    norm_num only [Nat.cast_ofNat] at hm
    linarith only [hm,corrected63_lower]

theorem harmonic_upper {n:ℕ} (hn:1≤n) : Harmonic n≤Real.log n+578/1000+1/(2*(n:ℝ)) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  by_cases h63:63≤n
  · have hm := corrected_harmonic_mono (M:=63) (by decide) h63
    norm_num only [Nat.cast_ofNat] at hm
    have hp : (1:ℝ)/(2*((n:ℝ)+1))≤1/(2*(n:ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith only [hn0]
    linarith only [hm,corrected63_upper,hp]
  · have hm := harmonic_trap_mono hn (by omega : n≤63)
    norm_num only [Nat.cast_ofNat] at hm
    linarith only [hm,corrected63_upper]

#print axioms harmonic_trap_step
#print axioms harmonic_trap_mono
#print axioms log63_upper
#print axioms corrected63_lower
#print axioms corrected63_upper
#print axioms harmonic_lower
#print axioms harmonic_upper
end
end JSP233.HarmonicWindow131
