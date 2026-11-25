module

public import Erdos272.Arithmetic.HarmonicCorrect118

@[expose] public section

namespace JSP233.EXHarmonic67702
open HarmonicAbel29
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem harmonic_log_step (n : ℕ) :
    Harmonic n-Real.log ((n : ℝ)+1) ≤
      Harmonic (n+1)-Real.log ((n : ℝ)+2) := by
  have hp : (0 : ℝ)<(n : ℝ)+1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (show (0 : ℝ)<(n : ℝ)+2 by positivity) hp)
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have he : ((n : ℝ)+2)/((n : ℝ)+1)-1=1/((n : ℝ)+1) := by
    field_simp
    ring
  rw [he] at hlog
  rw [HarmonicCorrect118.harmonic_successor]
  linarith only [hlog]

theorem harmonic_log_shift_mono {M N : ℕ} (hmn : M≤N) :
    Harmonic M-Real.log ((M : ℝ)+1) ≤ Harmonic N-Real.log ((N : ℝ)+1) := by
  induction N,hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
    have he : (((n+1 : ℕ) : ℝ)+1)=(n : ℝ)+2 := by push_cast;ring
    rw [he]
    exact ih.trans (harmonic_log_step n)

theorem harmonic_tail_error {M N : ℕ} {eta error : ℝ}
    (hmn : M≤N) (heta : 0<eta)
    (hcap : (M : ℝ)+1≤eta*((N : ℝ)+1)+error) :
    Real.log (1/eta)-error/(eta*((N : ℝ)+1)) ≤ Harmonic N-Harmonic M := by
  have hden : 0<eta*((N : ℝ)+1) := mul_pos heta (by positivity)
  have hmono := harmonic_log_shift_mono hmn
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (show (0 : ℝ)<(M : ℝ)+1 by positivity) hden)
  have hratio : ((M : ℝ)+1)/(eta*((N : ℝ)+1))-1≤error/(eta*((N : ℝ)+1)) := by
    apply (le_div_iff₀ hden).mpr
    have hc : (((M : ℝ)+1)/(eta*((N : ℝ)+1)))*(eta*((N : ℝ)+1))=(M : ℝ)+1 :=
      div_mul_cancel₀ _ hden.ne'
    nlinarith only [hcap,hc]
  have he : Real.log (((M : ℝ)+1)/(eta*((N : ℝ)+1)))=
      Real.log ((M : ℝ)+1)-Real.log eta-Real.log ((N : ℝ)+1) := by
    rw [Real.log_div (by positivity) hden.ne',Real.log_mul heta.ne' (by positivity)]
    ring
  have hone : Real.log (1/eta) = -Real.log eta := by
    rw [Real.log_div (by norm_num) heta.ne',Real.log_one]
    ring
  rw [he] at hlog
  rw [hone]
  linarith only [hmono,hlog,hratio]

theorem weighted_harmonic_tail {M N : ℕ} {eta error fee w : ℝ}
    (hmn : M≤N) (heta : 0<eta) (hw : 0≤w)
    (hcap : (M : ℝ)+1≤eta*((N : ℝ)+1)+error)
    (herror : w*error/(eta*((N : ℝ)+1))≤fee) :
    w*(Harmonic M-1)≤w*(Harmonic N-1-Real.log (1/eta))+fee := by
  have hh := mul_le_mul_of_nonneg_left (harmonic_tail_error hmn heta hcap) hw
  have he : w*(error/(eta*((N : ℝ)+1)))=w*error/(eta*((N : ℝ)+1)) := by ring
  rw [←he] at herror
  nlinarith only [hh,herror]

#print axioms harmonic_log_step
#print axioms harmonic_log_shift_mono
#print axioms harmonic_tail_error
#print axioms weighted_harmonic_tail
end
end JSP233.EXHarmonic67702
