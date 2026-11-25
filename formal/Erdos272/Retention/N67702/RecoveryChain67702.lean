module

public import Erdos272.Counting.N67702.EarlyChain67702
public import Erdos272.Retention.N109474.FringePlans109474
public import Erdos272.Arithmetic.N67702.NativeGates67702

@[expose] public section

namespace JSP233.RecoveryChain67702
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery67702 RecoveryCertificates67702 EarlyChain67702
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F⊆F :=
  EarlyChain67702.omitted_subset

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S∈Omitted N c F,¬IsAP S :=
  EarlyChain67702.omitted_bad

theorem span {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) : L+3≤R := by
  have hw := (middle g hN hhi).2
  have hn : (67702 : ℝ)≤N := by exact_mod_cast hN
  have hr : (L : ℝ)+3≤R := by dsimp only [Width] at hw;linarith only [hw,hn]
  exact_mod_cast hr

theorem short_profile {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {e : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (q : Fin 2) (hw : Width N L R≤EXOneHole67702.WidthCap q*N)
    (hj : 4≤j) (hjhi : j≤33) (hB : (38 : ℝ)≤BLocal 0 j)
    (hl : (L : ℝ)<(N : ℝ)/j) (he : ((Omitted N c F).card : ℝ)≤e) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+112/100)*N+(BLocal 0 j+1/2)*L+
      (HLocal 0-1-EXLog67702.Beta q)*Width N L R+874+e-c :=
  ProfileCount67702.actual_local_short_profile g hN hhi (middle g hN hhi).1
    (span g hN hhi) q hw hj hjhi hB hl he

theorem second_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ∀ S∈Omitted N c F,(33/100 : ℝ)*N<S.card := by
  have hs := middle g hN hhi
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hw : Width N L R≤EXOneHole67702.WidthCap 0*N := by
    norm_num [EXOneHole67702.WidthCap,EXOneHole67702.Numerator,EXOneHole67702.Denominator]
    linarith only [hs.2,hn0]
  have hp := short_profile (j:=15) g hN hhi 0 hw (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hs.1]) (middle_count g hN hhi)
  intro S hS
  have hh := JointDensity67702.actual_omitter_size (1 : Fin 3) g (k:=0) (by decide) hN hhi
    (by simpa [JointDensity67702.Left] using hs.1.le)
    (by simpa [JointDensity67702.parameters] using middle_count g hN hhi)
    (by
      dsimp only [JointDensity67702.parameters,CoarseW] at *
      norm_num [EXLog67702.Beta] at hp ⊢
      linarith only [hp])
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity67702.parameters] using hh

theorem strong_count {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ((Omitted N c F).card : ℝ)≤(2559/500 : ℝ)*N :=
  DenseCount67702.actual_strong_count hN (by omega) (omitted_legal g) omitted_bad
    (second_dense g hN hhi)

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    (L : ℝ)<(1/16 : ℝ)*N ∧ Width N L R<(11/100 : ℝ)*N := by
  have hs := middle g hN hhi
  have hn0 := Nat.cast_nonneg (α:=ℝ) N
  have hw : Width N L R≤EXOneHole67702.WidthCap 0*N := by
    norm_num [EXOneHole67702.WidthCap,EXOneHole67702.Numerator,EXOneHole67702.Denominator]
    linarith only [hs.2,hn0]
  have hp := short_profile (j:=15) g hN hhi 0 hw (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hs.1]) (strong_count g hN hhi)
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (strong_stage (k:=0) (by decide))
  dsimp only [StrongA,CoarseW] at *
  norm_num [EXLog67702.Beta] at hp ⊢
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ∀ S∈Omitted N c F,(1/3 : ℝ)*N<S.card := by
  have hs := strong g hN hhi
  have hw : Width N L R≤EXOneHole67702.WidthCap 1*N := by
    simpa [EXOneHole67702.WidthCap,EXOneHole67702.Numerator,EXOneHole67702.Denominator] using hs.2.le
  have hp := short_profile (j:=16) g hN hhi 1 hw (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hs.1]) (strong_count g hN hhi)
  intro S hS
  have hh := JointDensity67702.actual_omitter_size (2 : Fin 3) g (k:=0) (by decide) hN hhi
    (by simpa [JointDensity67702.Left] using hs.1.le)
    (by simpa [JointDensity67702.parameters] using strong_count g hN hhi)
    (by
      change Recovery208.WidthProfile (L : ℝ) (Width N L R) ≤
        StrongA 0*N+(BLocal 0 16-1/2+1)*L+
          (HLocal 0-42072/10000)*Width N L R+874-c
      norm_num [StrongA,EXLog67702.Beta] at hp ⊢
      linarith only [hp])
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity67702.parameters] using hh

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ∃ H∈F,IsAP H∧Finset.Icc (L : ℤ) (R : ℤ)⊆H := by
  have hi := RetainedIntervals67702.actual_avoiders_intervals g (by omega) (by omega) (middle g hN hhi).1
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  obtain ⟨H,hHG,hAP,hI⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H,(Finset.mem_sdiff.mp hHG).1,hAP,hI⟩

theorem prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    ((Omitted N c F).card : ℝ)≤(13/2 : ℝ)*Width N L R-11/2 := by
  have hp := FringePlans109474.preparation (by omega : 901≤N)
    (by have h:=g.root_left;omega) g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (strong g hN hhi).2
  simpa only [sub_eq_add_neg,neg_div] using hp

theorem fine_profile_at {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (hj : 4≤j) (hjhi : j≤33) (hB : (38 : ℝ)≤BLocal 0 j) (hl : (L : ℝ)<(N : ℝ)/j) :
    Recovery208.WidthProfile L (Width N L R)≤
      FineA 0*N+(BLocal 0 j+1/2)*L+FineW 0*Width N L R+FineC := by
  have hs := strong g hN hhi
  have hw : Width N L R≤EXOneHole67702.WidthCap 1*N := by
    simpa [EXOneHole67702.WidthCap,EXOneHole67702.Numerator,EXOneHole67702.Denominator] using hs.2.le
  have hp := short_profile g hN hhi 1 hw hj hjhi hB hl (prepared g hN hhi)
  dsimp only [FineA,FineW,FineC] at *
  norm_num [EXLog67702.Beta] at hp ⊢
  linarith only [hp,Nat.cast_nonneg (α:=ℝ) c]

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) :
    (L : ℝ)<(1/18 : ℝ)*N ∧ Width N L R<(3/32 : ℝ)*N := by
  apply Recovery208.actual_stage_bounds (show (Low 0 : ℝ)≤N by exact_mod_cast hN)
    (fine_final (k:=0) (by decide))
  exact fine_profile_at (j:=16) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by have h:=(strong g hN hhi).1;nlinarith only [h])

theorem native_gates {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) : CoreSupply86412.Native N L R := by
  have hs := final_bounds g hN hhi
  let w := L+N-R
  have hw : (w : ℝ)=Width N L R := by
    dsimp only [w,Width]
    rw [Nat.cast_sub (by have h:=g.right_ground;omega : R≤L+N)]
    push_cast
    ring
  have hwidth : 32*(L+N-R)≤3*N := by
    have h : (32 : ℝ)*(w : ℝ)≤3*N := by rw [hw];nlinarith only [hs.2]
    exact_mod_cast h
  have hp := fine_profile_at (j:=18) g hN hhi (by decide) (by decide)
    (by norm_num [BLocal,LogLocal,Lower,CovarianceScalar213.Polynomial])
    (by nlinarith only [hs.1])
  exact NativeGates67702.native_from_profile hN g.right_ground hwidth hp

#print axioms omitted_subset
#print axioms omitted_bad
#print axioms span
#print axioms short_profile
#print axioms second_dense
#print axioms strong_count
#print axioms strong
#print axioms strong_dense
#print axioms core
#print axioms prepared
#print axioms fine_profile_at
#print axioms final_bounds
#print axioms native_gates
end
end JSP233.RecoveryChain67702
