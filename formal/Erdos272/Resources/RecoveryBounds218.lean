import Erdos272.Counting.DensePair218
import Erdos272.Counting.UnitAvoider218
import Erdos272.Counting.FringeCount218
import Erdos272.Geometry.RetainedIntervals218
import Erdos272.Arithmetic.DirectMoment128

namespace JSP233.RecoveryBounds218
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
open InitialProfile218 RecoveryCaps213 Recovery208
open DensePair218 UnitCount218 UnitAvoider218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def StrongA : ℝ := HCap+229/50+28
def FinalA : ℝ := HCap+229/50
def FinalW : ℝ := HCap+1117/60
def LocalLog30 : ℝ := LogCap-17/5
def Local30 : ℝ := 102/25+2*(LocalLog30+1)+CovarianceScalar213.Polynomial LocalLog30

theorem log30_lower : (17/5 : ℝ)≤Real.log 30 := by
  have h2 := LogThree126.log_two_window.1
  have h3 := LogThree126.log_three_window.1
  have h5 := DirectMoment128.log_five_window.1
  have he : Real.log (30 : ℝ)=Real.log 2+Real.log 3+Real.log 5 := by
    rw [show (30 : ℝ)=2*3*5 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ)*3≠0) (by norm_num : (5 : ℝ)≠0),
      Real.log_mul (by norm_num : (2 : ℝ)≠0) (by norm_num : (3 : ℝ)≠0)]
  rw [he]
  norm_num [LogThree126.TwoLo,LogThree126.ThreeLo,DirectMoment128.FiveLo] at h2 h3 h5
  linarith only [h2,h3,h5]

theorem local30_payment {N L : ℕ} (hN : 642498≤N) (hhigh : N≤653292)
    (hL : 1≤L) (hleft : (L : ℝ)<(N : ℝ)/30) :
    (102/25+2*Harmonic L+CovarianceScalar213.Polynomial (Real.log L))*(L : ℝ)≤Local30*L := by
  have hc := RecoveryCaps213.actual_caps (by omega : 100000≤N) (by omega : N≤656184)
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hm : (L : ℝ)*30≤N := (le_div_iff₀ (by norm_num : (0 : ℝ)<30)).mp hleft.le
  have hl := Real.log_le_log (mul_pos hLp (by norm_num : (0 : ℝ)<30)) hm
  rw [Real.log_mul hLp.ne' (by norm_num : (30 : ℝ)≠0)] at hl
  have hcap : Real.log L≤LocalLog30 := by
    have hb := log30_lower
    have hn := hc.log_le
    dsimp only [LocalLog30]
    linarith only [hl,hb,hn]
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hp := RecoveryResource214.new_polynomial_mono
    (Real.log_nonneg (by exact_mod_cast hL)) hcap
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hcap hL0
  have h2 := mul_le_mul_of_nonneg_right hh hL0
  have h3 := mul_le_mul_of_nonneg_right hp hL0
  dsimp only [Local30]
  nlinarith only [h1,h2,h3]

theorem actual_strong_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    WidthProfile L ((L : ℝ)+(N-R))≤StrongA*N+Global*L+HCap*((L : ℝ)+(N-R))+875 := by
  have hua := actual_avoid_unit_width_count g
  have he := DensePair218.actual_E_bound hN hhigh g hua
  have hc := RecoveryCaps213.actual_caps (by omega : 100000≤N) (by omega : N≤656184)
  have hr := CovarianceFamily214.actual_original_raw_profile_local
    (by omega : 19≤N) (by omega : N≤720896) g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hL : 1≤L := by have hh := g.root_left; omega
  have hLN := g.left_right.trans g.right_ground
  have hhl := (ActualRecoveryChain208.harmonic_mono hLN).trans hc.harmonic_le
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hl := (Real.log_le_log hLp (show (L : ℝ)≤N by exact_mod_cast hLN)).trans hc.log_le
  have hp := RecoveryResource214.new_polynomial_mono
    (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hh : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hh,hL0]
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  have hhL := mul_le_mul_of_nonneg_right hhl hL0
  have hpoly := mul_le_mul_of_nonneg_right hp hL0
  dsimp only [CovarianceFamily214.MiddleCost,LocalRecovery208.GeometryCost] at hr
  dsimp only [StrongA,Global,DensePair218.Mu] at *
  nlinarith only [hr,he,hn,hw,hhL,hpoly]

theorem scalar_strong {n L w : ℝ} (hn : 642498≤n)
    (hp : WidthProfile L w≤StrongA*n+Global*L+HCap*w+875) :
    L<n/30 ∧ w<n/(37/2) := by
  have hc : StageCertificate 642498 StrongA Global HCap 875 (1/30) (2/37) := by
    norm_num [StageCertificate,StrongA,Global,HCap,LogCap,CovarianceScalar213.Polynomial,
      LeftCentre,WidthCentre,ShiftEnergy]
  have hs := actual_stage_bounds hn hc hp
  constructor <;> nlinarith only [hs.1,hs.2]

theorem actual_strong_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    (L : ℝ)<(N : ℝ)/30 ∧ (L : ℝ)+(N-R)<(N : ℝ)/(37/2) :=
  scalar_strong (by exact_mod_cast hN) (actual_strong_profile hN hhigh g)

theorem actual_E_dense6 {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    ∀S∈TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ),(N : ℝ)<6*S.card := by
  intro S hS
  have hua := actual_avoid_unit_width_count g
  have hSF := actual_deleted_subset N 11 F (Finset.mem_filter.mp hS).1
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hc := (Finset.mem_filter.mp hS).2
  have hs := DensePair218.actual_omitter_size hN hhigh g hua hSF hb hc
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  norm_num [DensePair218.Tau] at hs
  nlinarith only [hs,hn]

theorem actual_final_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    WidthProfile L ((L : ℝ)+(N-R))≤FinalA*N+Local30*L+FinalW*((L : ℝ)+(N-R))+875-197/20 := by
  have hs := actual_strong_bounds hN hhigh g
  have hL : 1≤L := by have hh := g.root_left; omega
  have hl : (L : ℝ)<(5/97 : ℝ)*N := by
    have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    nlinarith only [hs.1,hn]
  have hi := RetainedIntervals218.actual_avoiders_intervals g hN hhigh hl
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  obtain ⟨H,hHG,hHAP,hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 11 F) g.left_right hne hi
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀S∈E,¬IsAP S := fun S hS =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have he := FringeCount218.actual_preparation hN hL g.left_right g.right_ground g.legal hEF hbad
    (actual_E_dense6 hN hhigh g) ⟨H,(Finset.mem_sdiff.mp hHG).1,hHAP,hIH⟩ hs.2
  have hr := CovarianceFamily214.actual_original_raw_profile_local
    (by omega : 19≤N) (by omega : N≤720896) g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hc := RecoveryCaps213.actual_caps (by omega : 100000≤N) (by omega : N≤656184)
  have hp := local30_payment hN hhigh hL hs.1
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hh : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hh,hL0]
  have hn := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  have hw := mul_le_mul_of_nonneg_right hc.harmonic_le hw0
  dsimp only [CovarianceFamily214.MiddleCost,LocalRecovery208.GeometryCost] at hr
  dsimp only [FinalA,FinalW]
  change ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ)≤_ at he
  nlinarith only [hr,he,hp,hn,hw]

theorem scalar_final {n L w : ℝ} (hn : 642498≤n)
    (hp : WidthProfile L w≤FinalA*n+Local30*L+FinalW*w+875-197/20) :
    L<n/48 ∧ w<n/29 := by
  have hc : StageCertificate 642498 FinalA Local30 FinalW (875-197/20) (1/48) (1/29) := by
    norm_num [StageCertificate,FinalA,Local30,LocalLog30,FinalW,HCap,LogCap,
      CovarianceScalar213.Polynomial,LeftCentre,WidthCentre,ShiftEnergy]
  have hp' : WidthProfile L w≤FinalA*n+Local30*L+FinalW*w+(875-197/20) := by
    simpa only [add_sub_assoc] using hp
  have hs := actual_stage_bounds hn hc hp'
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hs

theorem actual_final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T) :
    (L : ℝ)<(N : ℝ)/48 ∧ (L : ℝ)+(N-R)<(N : ℝ)/29 :=
  scalar_final (by exact_mod_cast hN) (actual_final_profile hN hhigh g)

#print axioms actual_strong_profile
#print axioms actual_strong_bounds
#print axioms actual_E_dense6
#print axioms actual_final_profile
#print axioms actual_final_bounds
end
end JSP233.RecoveryBounds218
