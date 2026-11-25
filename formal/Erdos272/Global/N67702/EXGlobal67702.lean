module

public import Erdos272.Counting.N67702.EXTruncated67702
public import Erdos272.Arithmetic.N67702.EXHarmonic67702
public import Erdos272.Arithmetic.N67702.EXLog67702

@[expose] public section

namespace JSP233.EXGlobal67702
open StarCompletion APGeometry APCount41 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_four_width {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2000≤N) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S)
    (hfour : ∀ S∈F,4≤S.card) (hlarge : ∀ S∈F,2≤Step S)
    (hends : ∀ S∈F,Low S≤(L : ℤ) ∧ (R : ℤ)≤High S) :
    (F.card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+
      ((L : ℝ)+((N : ℝ)-R))*(Harmonic N-10493/5000)+(N : ℝ)/3 := by
  let D := (N-1)/3
  let w : ℝ := (L : ℝ)+((N : ℝ)-R)
  have hD : 1≤D := by dsimp only [D];omega
  have hDN : D≤N := by dsimp only [D];omega
  have h := EXTruncated67702.actual_truncated_count (M:=D) (J:=∅) hRN hD le_rfl
    hF hAP hfour hlarge hends (by simp) (by simp) (by
      intro d hd hDd
      have hdD := (Finset.mem_Icc.mp hd).2
      dsimp only [D] at hDd
      omega)
  have hDw : (3 : ℝ)*D≤(N : ℝ)-1 := by
    have hh : 3*D≤N-1 := by dsimp only [D];omega
    have hhR : (3 : ℝ)*D≤((N-1 : ℕ) : ℝ) := by exact_mod_cast hh
    rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one] at hhR
    exact hhR
  have hRNr : (R : ℝ)≤N := by exact_mod_cast hRN
  have hLRr : (L : ℝ)≤R := by exact_mod_cast hLR
  have hw : 0≤w := by dsimp only [w];positivity
  have hwN : w≤N := by dsimp only [w];linarith only [hLRr]
  have hcap : (D : ℝ)+1≤(1/3 : ℝ)*((N : ℝ)+1)+1/3 := by linarith only [hDw]
  have herr : w*(1/3 : ℝ)/((1/3)*((N : ℝ)+1))≤1 := by
    apply (div_le_iff₀ (show (0 : ℝ)<(1/3)*((N : ℝ)+1) by positivity)).mpr
    linarith only [hwN]
  have ht := EXHarmonic67702.weighted_harmonic_tail hDN (by norm_num : (0 : ℝ)<1/3)
    hw hcap herr
  norm_num only [one_div_div] at ht
  have hl := mul_le_mul_of_nonneg_left EXLog67702.log_three_lower hw
  norm_num only [Finset.card_empty,Nat.cast_zero,sub_zero] at h
  change (F.card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+w*(Harmonic D-1)+(D : ℝ)-1 at h
  dsimp only [w] at h ht hl ⊢
  nlinarith only [h,ht,hl,hDw]

#print axioms actual_four_width
end
end JSP233.EXGlobal67702
