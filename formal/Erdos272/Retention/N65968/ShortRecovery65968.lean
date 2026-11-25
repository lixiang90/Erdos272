module

public import Erdos272.Retention.N65968.ActualSupply65968
public import Erdos272.Retention.N109474.FringePlans109474
public import Erdos272.Retention.N291012.FringeGeneric291012
public import Erdos272.Retention.N67702.RetainedIntervals67702
public import Erdos272.Counting.N65968.ProfileCount65968
public import Erdos272.Retention.N65968.RecoveryCertificates65968
public import Erdos272.Counting.N65968.DenseCount65968
public import Erdos272.Retention.N65968.DensityRecovery65968
public import Erdos272.Counting.N65968.JointDensity65968

@[expose] public section

namespace JSP233.ShortRecovery65968
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery65968 RecoveryCertificates65968
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

theorem coarse_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ((Omitted N c F).card : ℝ)≤(1611/20 : ℝ)*N :=
  DenseCount65968.actual_omitted_count hN (by omega) g.legal

theorem global_seventh {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    (L : ℝ)<(1/7 : ℝ)*N := by
  have hp := ProfileCount65968.actual_global_profile g hN hhi (coarse_count g hN hhi)
  have hc0 := Nat.cast_nonneg (α:=ℝ) c
  have hprofile : Recovery208.WidthProfile (L : ℝ) (Width N L R)≤
      CoarseA 0*N+(BGlobal 0+1)*L+GlobalW 0*Width N L R+872 := by
    dsimp only [CoarseA,GlobalW]
    linarith only [hp,hc0]
  exact (Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (RecoveryCertificates65968.global_seventh (k:=0) (by decide)) hprofile).1

theorem first_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ∀ S∈Omitted N c F,(23/100 : ℝ)*N<S.card := by
  have hl := global_seventh g hN hhi
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hp := ProfileCount65968.actual_local_global_profile (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (coarse_count g hN hhi)
  intro S hS
  have hh := JointDensity65968.actual_omitter_size g (k:=0) (by decide) hN hhi
    (by simpa [JointDensity65968.Left] using hl.le)
    (by simpa [JointDensity65968.parameters] using coarse_count g hN hhi)
    (by
      norm_num [JointDensity65968.parameters,CoarseA,GlobalW] at hp ⊢
      linarith only [hp,Nat.cast_nonneg (α:=ℝ) c])
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity65968.parameters] using hh

theorem first_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ((Omitted N c F).card : ℝ)≤(53/5 : ℝ)*N :=
  DenseCount65968.actual_first_count hN (by omega) (omitted_legal g) omitted_bad (first_dense g hN hhi)

theorem first {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    (L : ℝ)<(1/13 : ℝ)*N ∧ Width N L R<(1/8 : ℝ)*N := by
  have hl := global_seventh g hN hhi
  have hp := ProfileCount65968.actual_local_global_profile (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (first_count g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (first_thirteenth (k:=0) (by decide))
  dsimp only [FirstA,GlobalW] at *
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem intermediate_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ∀ S∈Omitted N c F,(61/200 : ℝ)*N<S.card := by
  have hs := first g hN hhi
  intro S hS
  exact DensityRecovery65968.actual_omitter_size g (k:=0) (by decide) hN hhi hs.1 hs.2
    (by simpa only [zero_mul,add_zero] using first_count g hN hhi)
    (DensityRecovery65968.intermediate_gate (k:=0) (by decide)) (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem middle_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ((Omitted N c F).card : ℝ)≤(6 : ℝ)*N :=
  DenseCount65968.actual_three_tenths_count hN (by omega) (omitted_legal g) omitted_bad
    (intermediate_dense g hN hhi)

theorem middle {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    (L : ℝ)<(1/15 : ℝ)*N ∧ Width N L R<(23/200 : ℝ)*N := by
  have hl := (first g hN hhi).1
  have hp := ProfileCount65968.actual_local_global_profile (j:=13) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (middle_count g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (middle_short (k:=0) (by decide))
  dsimp only [MiddleA,GlobalW] at *
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ∃ H∈F,IsAP H∧Finset.Icc (L : ℤ) (R : ℤ)⊆H := by
  have hi := RetainedIntervals67702.actual_avoiders_intervals g (by omega) (by omega) (middle g hN hhi).1
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  obtain ⟨H,hHG,hAP,hI⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H,(Finset.mem_sdiff.mp hHG).1,hAP,hI⟩

def WeakPlan (d : ℕ) : ℕ := if d=1 then 5 else 4

theorem span {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) : L+3≤R := by
  have hw:=(middle g hN hhi).2
  have hn : (63616 : ℝ)≤N := by exact_mod_cast hN
  have hr : (L : ℝ)+3≤R := by dsimp only [Width] at hw;linarith only [hw,hn]
  exact_mod_cast hr

theorem weak_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ((Omitted N c F).card : ℝ)≤(53/6 : ℝ)*Width N L R-13/2 := by
  have hn : (63616 : ℝ)≤N := by exact_mod_cast hN
  have hs:=middle g hN hhi
  have hplan : ∀ d∈Finset.Icc 1 (4-1), d<WeakPlan d ∧
      AlignedPlans212.GateConstant d (WeakPlan d)<
        (N : ℝ)*AlignedPlans212.GateCoefficient (200/61) (200/23) d (WeakPlan d) := by
    intro d hd
    obtain ⟨hd1,hd2⟩:=Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [WeakPlan,AlignedPlans212.GateConstant,AlignedPlans212.GateCoefficient] <;>
      linarith only [hn]
  have hoff : ((5 : ℝ)-1)*((5 : ℝ)-2)/2<
      (N : ℝ)*((5 : ℝ)/(200/61)-1-((5 : ℝ)-1)/(200/23)) := by
    norm_num
    linarith only [hn]
  have hh:=FringeGeneric291012.actual_fringe_count
    (K:=4) (k:=(200/61 : ℝ)) (p:=5) (u:=(200/23 : ℝ)) WeakPlan
    (by norm_num) (by norm_num) (by decide) (by have h:=g.root_left;omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (by intro S hS;have hd:=intermediate_dense g hN hhi S hS;nlinarith only [hd])
    (core g hN hhi) (by dsimp only [Width] at *;nlinarith only [hs.2]) hplan hoff
  norm_num [AlignedPlans212.Slope,AlignedPlans212.Constant,WeakPlan,Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    (L : ℝ)<(3/50 : ℝ)*N ∧ Width N L R<(51/500 : ℝ)*N := by
  have hs:=middle g hN hhi
  have hw : Width N L R≤EXOneHole67702.WidthCap 0*N := by
    simpa [EXOneHole67702.WidthCap,EXOneHole67702.Numerator,EXOneHole67702.Denominator] using hs.2.le
  have hp:=ProfileCount65968.actual_local_short_profile (j:=15) g hN hhi hs.1
    (span g hN hhi) 0 hw (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hs.1]) (weak_prepared g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (weak_box (k:=0) (by decide))
  dsimp only [WeakA,WeakW,WeakC]
  norm_num [EXLog67702.Beta] at hp
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ∀ S∈Omitted N c F,(1/3 : ℝ)*N<S.card := by
  have hs:=strong g hN hhi
  intro S hS
  exact DensityRecovery65968.actual_omitter_size g (k:=0) (by decide) hN hhi hs.1 hs.2
    (by simpa only [zero_mul,zero_add,sub_eq_add_neg,neg_div] using weak_prepared g hN hhi)
    (DensityRecovery65968.strong_gate (k:=0) (by decide)) (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    ((Omitted N c F).card : ℝ)≤(13/2 : ℝ)*Width N L R-11/2 := by
  have hs:=strong g hN hhi
  have hn:=Nat.cast_nonneg (α:=ℝ) N
  have hp:=FringePlans109474.preparation (by omega : 901≤N)
    (by have h:=g.root_left;omega) g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (by linarith only [hs.2,hn])
  simpa only [sub_eq_add_neg,neg_div] using hp

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) :
    (L : ℝ)<(3/50 : ℝ)*N ∧ Width N L R<(51/500 : ℝ)*N := strong g hN hhi

theorem native_gates {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 63616≤N) (hhi : N≤67701) : ActualSupply65968.Core N L R := by
  have hs:=strong g hN hhi
  let w:=L+N-R
  have hw : (w : ℝ)=Width N L R := by
    dsimp only [w,Width]
    rw [Nat.cast_sub (by have h:=g.right_ground;omega : R≤L+N)]
    push_cast
    ring
  have hL:=hs.1.le
  have hW:=hs.2.le
  rw [←hw] at hW
  apply ActualSupply65968.of_gates (by omega : N<510510)
  constructor
  · have hp : (105 : ℝ)*(809*L+1193*w)≤19159*N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (11 : ℝ)*L+19*w≤3*N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (8 : ℝ)*L+4*w≤N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (210 : ℝ)*(1001*L+192*w)≤39319*N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (2 : ℝ)*(15*L+4*w)≤7*N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (3 : ℝ)*L+4*w≤N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (L : ℝ)+w≤N := by nlinarith only [hL,hW]
    exact_mod_cast hp
  · have hp : (3 : ℝ)*w≤N := by nlinarith only [hL,hW]
    exact_mod_cast hp

#print axioms omitted_subset
#print axioms omitted_bad
#print axioms omitted_legal
#print axioms coarse_count
#print axioms global_seventh
#print axioms first_dense
#print axioms first_count
#print axioms first
#print axioms intermediate_dense
#print axioms middle_count
#print axioms middle
#print axioms core
#print axioms span
#print axioms weak_prepared
#print axioms strong
#print axioms strong_dense
#print axioms prepared
#print axioms final_bounds
#print axioms native_gates
end
end JSP233.ShortRecovery65968
