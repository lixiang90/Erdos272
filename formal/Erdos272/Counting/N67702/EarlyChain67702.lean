module

public import Erdos272.Counting.N67702.ProfileCount67702
public import Erdos272.Retention.N67702.RecoveryCertificates67702
public import Erdos272.Counting.N67702.DenseCount67702
public import Erdos272.Retention.N67702.DensityRecovery67702
public import Erdos272.Counting.N67702.JointDensity67702

@[expose] public section

namespace JSP233.EarlyChain67702
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery67702 RecoveryCertificates67702
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
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ((Omitted N c F).card : ℝ)≤(80489/1000 : ℝ)*N :=
  DenseCount67702.actual_omitted_count hN (by omega) g.legal

theorem global_seventh {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    (L : ℝ)<(1/7 : ℝ)*N := by
  have hp := ProfileCount67702.actual_global_profile g hN hhi (coarse_count g hN hhi)
  have hc0 := Nat.cast_nonneg (α:=ℝ) c
  have hprofile : Recovery208.WidthProfile (L : ℝ) (Width N L R)≤
      CoarseA 0*N+(BGlobal 0+1)*L+GlobalW 0*Width N L R+872 := by
    dsimp only [CoarseA,GlobalW]
    linarith only [hp,hc0]
  exact (Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (RecoveryCertificates67702.global_seventh (k:=0) (by decide)) hprofile).1

theorem first_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ∀ S∈Omitted N c F,(47/200 : ℝ)*N<S.card := by
  have hl := global_seventh g hN hhi
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hp := ProfileCount67702.actual_local_global_profile (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (coarse_count g hN hhi)
  intro S hS
  have hh := JointDensity67702.actual_omitter_size (0 : Fin 3) g (k:=0) (by decide) hN hhi
    (by simpa [JointDensity67702.Left] using hl.le)
    (by simpa [JointDensity67702.parameters] using coarse_count g hN hhi)
    (by
      norm_num [JointDensity67702.parameters,CoarseA,GlobalW] at hp ⊢
      linarith only [hp,Nat.cast_nonneg (α:=ℝ) c])
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity67702.parameters] using hh

theorem first_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ((Omitted N c F).card : ℝ)≤(1262/125 : ℝ)*N :=
  DenseCount67702.actual_first_count hN (by omega) (omitted_legal g) omitted_bad (first_dense g hN hhi)

theorem first {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    (L : ℝ)<(1/14 : ℝ)*N ∧ Width N L R<(1/8 : ℝ)*N := by
  have hl := global_seventh g hN hhi
  have hp := ProfileCount67702.actual_local_global_profile (j:=7) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (first_count g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (first_stage (k:=0) (by decide))
  dsimp only [FirstA,GlobalW] at *
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem intermediate_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ∀ S∈Omitted N c F,(3/10 : ℝ)*N<S.card := by
  have hs := first g hN hhi
  intro S hS
  exact DensityRecovery67702.actual_omitter_size g (k:=0) (by decide) hN hhi hs.1 hs.2
    (by simpa only [zero_mul,add_zero] using first_count g hN hhi)
    (DensityRecovery67702.intermediate_gate (k:=0) (by decide)) (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem middle_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ((Omitted N c F).card : ℝ)≤(6193/1000 : ℝ)*N :=
  DenseCount67702.actual_three_tenths_count hN (by omega) (omitted_legal g) omitted_bad
    (intermediate_dense g hN hhi)

theorem middle {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    (L : ℝ)<(1/15 : ℝ)*N ∧ Width N L R<(14/125 : ℝ)*N := by
  have hl := (first g hN hhi).1
  have hp := ProfileCount67702.actual_local_global_profile (j:=14) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hl]) (middle_count g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (middle_stage (k:=0) (by decide))
  dsimp only [MiddleA,GlobalW] at *
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

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
end
end JSP233.EarlyChain67702
