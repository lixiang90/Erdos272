module

public import Erdos272.Resources.N80470.LocalRecovery80470
public import Erdos272.Retention.N80470.RecoveryCertificates80470
public import Erdos272.Counting.N80470.DenseCount80470
public import Erdos272.Retention.N80470.DensityRecovery80470
public import Erdos272.Counting.N80470.JointDensity80470
public import Erdos272.Counting.N80470.RootedProfile80470
public import Erdos272.Retention.N109474.FringePlans109474
public import Erdos272.Arithmetic.N80470.NativeGates80470

@[expose] public section

namespace JSP233.RecoveryChain80470
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery80470 RecoveryCertificates80470
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F⊆F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S∈Omitted N c F,¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

theorem omitted_legal {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) : Legal (Ground N) (Omitted N c F) :=
  ⟨fun S hS => g.legal.1 S (omitted_subset hS),
   fun S hS U hU hSU => g.legal.2 S (omitted_subset hS) U (omitted_subset hU) hSU⟩

theorem raw_profile_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {rho : ℝ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425)
    (he : ((Omitted N c F).card : ℝ)≤rho*N) :
    RawProfile N L (Width N L R) (HLocal 0+433/100+rho) (HLocal 0) 872 := by
  have hc := LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega : 10000≤N) hhi
  have hr := GenericRecovery291012.actual_original_raw_profile_local (by omega : 19≤N)
    (by omega : N≤720896) g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground
    g.root g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α:=ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  change ((TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)).card : ℝ)≤_ at he
  dsimp only [RawProfile,Coeff,Width,CovarianceFamily214.MiddleCost,LocalRecovery208.GeometryCost] at *
  nlinarith only [hr,he,hnpaid,hwpaid]

theorem local_profile_count {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {rho : ℝ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425)
    (hj : 4≤j) (hjhi : j≤33) (hB : (38 : ℝ)≤BLocal 0 j)
    (hleft : (L : ℝ)<(N : ℝ)/j) (he : ((Omitted N c F).card : ℝ)≤rho*N) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+433/100+rho)*N+BLocal 0 j*L+HLocal 0*Width N L R+872 := by
  exact local_profile (k:=0) (j:=j) (LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega) hhi)
    (by have h:=g.root_left; omega) hj hjhi hB hleft (raw_profile_count g hN hhi he)

theorem coarse_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ((Omitted N c F).card : ℝ)≤(1609/20 : ℝ)*N :=
  DenseCount80470.actual_omitted_count hN (by omega) g.legal

theorem global_seventh {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    (L : ℝ)<(1/7 : ℝ)*N := by
  have hp := global_profile (k:=0) (LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega) hhi)
    (by have h:=g.root_left; omega) (g.left_right.trans g.right_ground)
    (raw_profile_count g hN hhi (coarse_count g hN hhi))
  have hs := Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (RecoveryCertificates80470.global_seventh (k:=0) (by decide))
    (by simpa only [CoarseA] using hp)
  exact hs.1

theorem first_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∀ S∈Omitted N c F,(31/125 : ℝ)*N<S.card := by
  have hl := global_seventh g hN hhi
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hp := local_profile_count (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (coarse_count g hN hhi)
  intro S hS
  have hh := JointDensity80470.actual_omitter_size (0 : Fin 3) g (k:=0) (by decide) hN hhi
    (by nlinarith only [hl,hn0])
    (by simpa [JointDensity80470.parameters] using coarse_count g hN hhi)
    (by simpa [JointDensity80470.parameters,CoarseA] using hp)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity80470.parameters] using hh

theorem first_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ((Omitted N c F).card : ℝ)≤(9063/1000 : ℝ)*N :=
  DenseCount80470.actual_first_count hN (by omega) (omitted_legal g) omitted_bad (first_dense g hN hhi)

theorem first {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    (L : ℝ)<(1/14 : ℝ)*N ∧ Width N L R<(23/200 : ℝ)*N := by
  have hl := global_seventh g hN hhi
  have hp := local_profile_count (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (first_count g hN hhi)
  exact Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (first_stage (k:=0) (by decide)) (by simpa only [FirstA] using hp)

theorem intermediate_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∀ S∈Omitted N c F,(3/10 : ℝ)*N<S.card := by
  have hs := first g hN hhi
  intro S hS
  exact DensityRecovery80470.actual_omitter_size g (k:=0) (by decide) hN hhi hs.1 hs.2
    (by simpa only [zero_mul,add_zero] using first_count g hN hhi)
    (DensityRecovery80470.intermediate_gate (k:=0) (by decide)) (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem middle_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ((Omitted N c F).card : ℝ)≤(1239/200 : ℝ)*N :=
  DenseCount80470.actual_three_tenths_count hN (by omega) (omitted_legal g) omitted_bad
    (intermediate_dense g hN hhi)

theorem middle {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    (L : ℝ)<(1/15 : ℝ)*N ∧ Width N L R<(11/100 : ℝ)*N := by
  have hl := (first g hN hhi).1
  have hp := local_profile_count (j:=14) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (middle_count g hN hhi)
  exact Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (middle_stage (k:=0) (by decide)) (by simpa only [MiddleA] using hp)

theorem second_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∀ S∈Omitted N c F,(8/25 : ℝ)*N<S.card := by
  have hl := (middle g hN hhi).1
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hp := local_profile_count (j:=15) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (middle_count g hN hhi)
  intro S hS
  have hh := JointDensity80470.actual_omitter_size (1 : Fin 3) g (k:=0) (by decide) hN hhi
    (by nlinarith only [hl,hn0])
    (by simpa [JointDensity80470.parameters] using middle_count g hN hhi)
    (by simpa [JointDensity80470.parameters,MiddleA] using hp)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity80470.parameters] using hh

theorem strong_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ((Omitted N c F).card : ℝ)≤(109/20 : ℝ)*N :=
  DenseCount80470.actual_strong_count hN (by omega) (omitted_legal g) omitted_bad (second_dense g hN hhi)

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    (L : ℝ)<(1/16 : ℝ)*N ∧ Width N L R<(11/100 : ℝ)*N := by
  have hl := (middle g hN hhi).1
  have hp := local_profile_count (j:=15) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (strong_count g hN hhi)
  exact Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (strong_stage (k:=0) (by decide)) (by simpa only [StrongA] using hp)

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∀ S∈Omitted N c F,(1/3 : ℝ)*N<S.card := by
  have hl := (strong g hN hhi).1
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hp := local_profile_count (j:=16) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (strong_count g hN hhi)
  intro S hS
  have hh := JointDensity80470.actual_omitter_size (2 : Fin 3) g (k:=0) (by decide) hN hhi
    (by nlinarith only [hl,hn0])
    (by simpa [JointDensity80470.parameters] using strong_count g hN hhi)
    (by simpa [JointDensity80470.parameters,StrongA] using hp)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity80470.parameters] using hh

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∃ H∈F,IsAP H∧Finset.Icc (L : ℤ) (R : ℤ)⊆H := by
  have hs := strong g hN hhi
  have hi := RetainedIntervals86412.actual_avoiders_intervals g (by omega) (by omega) hs.1
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  obtain ⟨H,hHG,hAP,hI⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H,(Finset.mem_sdiff.mp hHG).1,hAP,hI⟩

theorem prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ((Omitted N c F).card : ℝ)≤(13/2 : ℝ)*Width N L R-11/2 := by
  have hp := FringePlans109474.preparation (by omega : 901≤N)
    (by have h:=g.root_left; omega) g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (strong g hN hhi).2
  simpa only [sub_eq_add_neg,neg_div] using hp

theorem small_root {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    ∀ S∈APPrepare49.SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ)),(c : ℤ)∈S := by
  have hw := (strong g hN hhi).2
  have hn : (80470 : ℝ)≤N := by exact_mod_cast hN
  have hspan : L+3≤R := by
    have hr : (L : ℝ)+3≤R := by dsimp only [Width] at hw; linarith only [hw,hn]
    exact_mod_cast hr
  exact RootedProfile80470.actual_small_root g (by omega) (by omega) (strong g hN hhi).1 hspan

theorem fine_raw {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    RawProfile N L (Width N L R) (FineA 0) (FineW 0) FineC := by
  have hc := LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega) hhi
  have hr := RootedProfile80470.actual_raw g (by omega) (by omega) (small_root g hN hhi)
  have he := prepared g hN hhi
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α:=ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  dsimp only [RawProfile,Coeff,Width,FineA,FineW,FineC,CovarianceFamily214.MiddleCost,
    LocalRecovery208.GeometryCost] at *
  nlinarith only [hr,he,hnpaid,hwpaid]

theorem fine_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    Recovery208.WidthProfile L (Width N L R)≤FineA 0*N+BLocal 0 16*L+FineW 0*Width N L R+FineC := by
  exact local_profile (k:=0) (j:=16) (LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega) hhi)
    (by have h:=g.root_left; omega) (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by have h:=(strong g hN hhi).1; nlinarith only [h]) (fine_raw g hN hhi)

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    (L : ℝ)<(1/18 : ℝ)*N ∧ Width N L R<(3/32 : ℝ)*N :=
  Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (fine_final (k:=0) (by decide)) (fine_profile g hN hhi)

theorem native_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) :
    Recovery208.WidthProfile L (Width N L R)≤FineA 0*N+BLocal 0 18*L+FineW 0*Width N L R+FineC := by
  exact local_profile (k:=0) (j:=18) (LocalRecovery80470.actual_caps (k:=0) (by decide) (by omega) hhi)
    (by have h:=g.root_left; omega) (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by have h:=(final_bounds g hN hhi).1; nlinarith only [h]) (fine_raw g hN hhi)

theorem native_gates {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 80470≤N) (hhi : N≤82425) : CoreSupply86412.Native N L R := by
  have hs := final_bounds g hN hhi
  let w := L+N-R
  have hw : (w : ℝ)=Width N L R := by
    dsimp only [w,Width]
    rw [Nat.cast_sub (by have h:=g.right_ground; omega : R≤L+N)]
    push_cast
    ring
  have hwidth : 32*(L+N-R)≤3*N := by
    have h : (32 : ℝ)*(w : ℝ)≤3*N := by rw [hw]; nlinarith only [hs.2]
    exact_mod_cast h
  exact NativeGates80470.native_from_profile hN g.right_ground hwidth (native_profile g hN hhi)

#print axioms omitted_subset
#print axioms omitted_bad
#print axioms omitted_legal
#print axioms raw_profile_count
#print axioms local_profile_count
#print axioms coarse_count
#print axioms global_seventh
#print axioms first_dense
#print axioms first_count
#print axioms first
#print axioms intermediate_dense
#print axioms middle_count
#print axioms middle
#print axioms second_dense
#print axioms strong_count
#print axioms strong
#print axioms strong_dense
#print axioms core
#print axioms prepared
#print axioms small_root
#print axioms fine_raw
#print axioms fine_profile
#print axioms final_bounds
#print axioms native_profile
#print axioms native_gates
end
end JSP233.RecoveryChain80470
