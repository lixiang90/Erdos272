import Erdos272.Resources.RecoveryResource213
import Erdos272.Resources.CovarianceFamily214
namespace JSP233.RecoveryResource214
open StarCompletion APGeometry HarmonicAbel29 DenseDeletion40
open LocalRecovery208 Recovery208 RecoveryCaps213 AlignedPlans212
open RecoveryResource213 (InitialGeometry Geometry)
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def C (r : ℕ) : ℝ := RecoveryCaps213.C r+847
def LocalCoeff (ell : ℝ) (j : ℕ) : ℝ :=
  102/25+2*(LocalLog ell j+1)+CovarianceScalar213.Polynomial (LocalLog ell j)
def GlobalCoeff (ell h : ℝ) : ℝ := 102/25+2*h+CovarianceScalar213.Polynomial ell

theorem new_polynomial_mono {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    CovarianceScalar213.Polynomial x≤CovarianceScalar213.Polynomial y := by
  dsimp only [CovarianceScalar213.Polynomial]
  gcongr

theorem local_payment {ell h : ℝ} {N L j : ℕ} (hc : Caps ell h N) (hL : 1≤L)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j) :
    (102/25+2*Harmonic L+CovarianceScalar213.Polynomial (Real.log L))*(L : ℝ) ≤
      LocalCoeff ell j*L := by
  have hl := RecoveryCaps213.log_local hc hL hj hleft
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hp := new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have h1 := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) L)
  have h2 := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) L)
  have h3 := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [LocalCoeff]
  nlinarith only [h1,h2,h3]
theorem initial_global_affine {ell h : ℝ} {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hc : Caps ell h N) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ A h 0*N+GlobalCoeff ell h*L+
      W h 0*((L : ℝ)+(N-R))+C 0 := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hLN := g.left_right.trans g.right_ground
  have hhl := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hl := (Real.log_le_log hLp (show (L : ℝ)≤N by exact_mod_cast hLN)).trans hc.log_le
  have hpoly := new_polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hr := CovarianceFamily214.actual_original_initial_profile_local (by omega : 10902≤N) (by omega : N≤720896)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hL0,hRN]
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  have hll := mul_le_mul_of_nonneg_right hhl hL0
  have hpl := mul_le_mul_of_nonneg_right hpoly hL0
  norm_num [A,W,C,RecoveryCaps213.C,GlobalCoeff]
  nlinarith only [hr,hn,hw,hll,hpl]

theorem initial_reprice {ell h : ℝ} {N c L R j : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hc : Caps ell h N)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ A h 0*N+
      LocalCoeff ell j*L+W h 0*((L : ℝ)+(N-R))+C 0 := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hl := local_payment hc hL hj hleft
  have hr := CovarianceFamily214.actual_original_initial_profile_local (by omega : 10902≤N) (by omega : N≤720896)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α := ℝ) N)
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
    linarith only [hRN,hL0]
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  norm_num [A,W,C,RecoveryCaps213.C]
  nlinarith only [hr,hl,hn,hw]

theorem actual_local_affine {ell h : ℝ} {N c L R r j : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hc : Caps ell h N)
    (hr1 : 1≤r) (hr3 : r≤3) (hj : j≤7)
    (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth r) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ A h r*N+
      LocalCoeff ell j*L+W h r*((L : ℝ)+(N-R))+C r := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hl := local_payment hc hL hj hleft
  have he := RecoveryOmitters213.actual_preparation_omission_count (c := c) g.low hr1 hr3 hL
    g.left_right g.right_ground g.legal g.interval_core hwidth
  have hr := CovarianceFamily214.actual_original_raw_profile_local (by omega : 19≤N) (by omega : N≤720896)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
    linarith only [hRN,hL0]
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  dsimp only [CovarianceFamily214.MiddleCost,GeometryCost] at hr
  have hr0 : r≠0 := by omega
  simp only [A,W,C,RecoveryCaps213.C,if_neg hr0]
  nlinarith only [hr,he,hn,hw,hl,hN0]
#print axioms new_polynomial_mono
#print axioms local_payment
#print axioms initial_global_affine
#print axioms initial_reprice
#print axioms actual_local_affine
end
end JSP233.RecoveryResource214
