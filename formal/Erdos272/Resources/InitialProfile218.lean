import Erdos272.Resources.CovarianceFamily214
import Erdos272.Arithmetic.RecoveryCaps213
import Erdos272.Resources.RecoveryResource214

namespace JSP233.InitialProfile218
open StarCompletion APGeometry HarmonicAbel29 DenseDeletion40
open Recovery208 RecoveryCaps213 LocalResourceRecovery208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Start (N c L R : ℕ) (F : Finset (Finset ℤ))
    (P T : Finset ℤ) : Prop where
  root_mem : (c : ℤ) ∈ Ground N
  legal : Legal (Ground N) F
  near_card : B N ≤ F.card
  root_left : c < L
  left_right : L ≤ R
  right_ground : R ≤ N
  root : ∀S∈Retained N 11 F, ¬IsAP S → (c : ℤ)∈S
  right_member : P∈Retained N 11 F
  right_avoids : (c : ℤ)∉P
  right_lower : ∀z∈P, (L : ℤ)≤z
  left_member : T∈Retained N 11 F
  left_avoids : (c : ℤ)∉T
  left_upper : ∀z∈T, z≤(R : ℤ)
  outside : ∀S∈Retained N 11 F, (c : ℤ)∉S →
    (∃u∈S,u≤(L : ℤ)) ∧ ∃v∈S,(R : ℤ)≤v

def Global : ℝ := 102/25+2*HCap+CovarianceScalar213.Polynomial LogCap

theorem actual_coarse_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (HCap+6279/50)*(N : ℝ)+Global*L+HCap*((L : ℝ)+(N-R))+1843 := by
  have hc := RecoveryCaps213.actual_caps (by omega : 100000≤N) (by omega : N≤656184)
  have hL : 1≤L := by have hcL := g.root_left; omega
  have hLN := g.left_right.trans g.right_ground
  have hhl := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hl := (Real.log_le_log hLp (show (L : ℝ)≤N by exact_mod_cast hLN)).trans hc.log_le
  have hp := RecoveryResource214.new_polynomial_mono
    (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hr := CovarianceFamily214.actual_original_initial_profile_local
    (by omega : 10902≤N) (by omega : N≤720896) g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hh : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hh,hL0]
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  have hhL := mul_le_mul_of_nonneg_right hhl hL0
  have hpoly := mul_le_mul_of_nonneg_right hp hL0
  dsimp only [Global]
  nlinarith only [hr,hn,hw,hhL,hpoly]

theorem scalar_coarse {n L w : ℝ} (hn : 642498≤n)
    (hp : WidthProfile L w ≤ (HCap+6279/50)*n+Global*L+HCap*w+1843) :
    L<n/18 ∧ w<n/10 := by
  have hcert : StageCertificate 642498 (HCap+6279/50) Global HCap 1843 (1/18) (1/10) := by
    norm_num [StageCertificate,Global,HCap,LogCap,CovarianceScalar213.Polynomial,
      LeftCentre,WidthCentre,ShiftEnergy]
  have hs := actual_stage_bounds hn hcert hp
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hs

theorem actual_coarse_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    (L : ℝ)<(N : ℝ)/18 ∧ (L : ℝ)+(N-R)<(N : ℝ)/10 := by
  exact scalar_coarse (by exact_mod_cast hN) (actual_coarse_profile hN hhigh g)

#print axioms actual_coarse_profile
#print axioms scalar_coarse
#print axioms actual_coarse_bounds
end
end JSP233.InitialProfile218
