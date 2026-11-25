module

public import Erdos272.Counting.N82426.PointProfile82426

@[expose] public section

set_option Elab.async false

namespace JSP233.PointRecovery82426
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery82427 RecoveryCertificates82427
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem coarse_profile {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    RawProfile 82426 L (Width 82426 L R) (CoarseA 0) (HLocal 0) 872 := by
  have he : ((Omitted 82426 c F).card : ℝ) ≤ (1609/20 : ℝ)*82426 := by
    exact_mod_cast PointArithmetic82426.actual_omitted_count g.legal
  have hp := raw_profile_lower (alpha := 1609/20) (beta := 0) (constant := 0) g
    (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA]

theorem global_seventh {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    (L : ℝ) < (1/7 : ℝ)*82426 := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := global_profile hc (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile g)
  exact (Recovery208.actual_stage_bounds
    (by norm_num : (82426 : ℝ)≤82426)
    (PointArithmetic82426.global_seventh) hp).1

theorem coarse {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    (L : ℝ) < (1/8 : ℝ)*82426 ∧ Width 82426 L R < (1 : ℝ)*82426 := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 7)
    (by decide : 7 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using global_seventh g) (coarse_profile g)
  exact Recovery208.actual_stage_bounds
    (by norm_num : (82426 : ℝ)≤82426) (PointArithmetic82426.coarse_local) hp

theorem coarse_dense {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ∀ S∈Omitted 82426 c F, (1/4 : ℝ)*82426<S.card := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hleft := (coarse g).1
  have hn : (0 : ℝ)≤82426 := Nat.cast_nonneg 82426
  have hp := local_profile hc (by have h:=g.root_left; omega) (by decide : 4≤8)
    (by decide : 8≤33)
    (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by nlinarith only [hleft]) (coarse_profile g)
  have he := PointArithmetic82426.actual_omitted_count (c := c) g.legal
  intro S hS
  have hh := PointArithmetic82426.joint_omitter (0 : Fin 2) g
    (by nlinarith only [hleft, hn]) (by simpa [JointDensity82427.parameters] using he)
    (by simpa [JointDensity82427.parameters] using hp)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity82427.parameters] using hh

theorem quarter_omitted {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ((Omitted 82426 c F).card : ℝ) ≤ (223/25 : ℝ)*82426 := by
  let E := Omitted 82426 c F
  have hEF : E ⊆ F := omitted_subset
  have hlegal : Legal (Ground 82426) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  have hbad : ∀ S ∈ E, ¬IsAP S := omitted_bad
  have hdense : ∀ S ∈ E, (82426 : ℝ)/4 < S.card := by
    intro S hS
    have h := coarse_dense g S hS
    nlinarith only [h]
  exact_mod_cast PointArithmetic82426.actual_quarter_count hlegal hbad (by intro S hS; have hd := hdense S hS; nlinarith only [hd])

theorem quarter {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    (L : ℝ) < (17/250 : ℝ)*82426 ∧ Width 82426 L R < (14/125 : ℝ)*82426 := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_lower (alpha := 223/25) (beta := 0) (constant := 0) g
    (by simpa only [zero_mul, add_zero] using quarter_omitted g)
  have hp' : RawProfile 82426 L (Width 82426 L R) (QuarterA 0) (HLocal 0) 872 := by
    convert hp using 1 <;> norm_num [QuarterA]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 8)
    (by decide : 8 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using (coarse g).1) hp'
  exact Recovery208.actual_stage_bounds
    (by norm_num : (82426 : ℝ)≤82426) (PointArithmetic82426.quarter_stage) hs

theorem intermediate_dense {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ∀ S∈Omitted 82426 c F, (3/10 : ℝ)*82426<S.card := by
  intro S hS
  exact PointArithmetic82426.intermediate_omitter g (quarter g).1 (quarter g).2
    (quarter_omitted g) (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2


theorem strong_omitted {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ((Omitted 82426 c F).card : ℝ)≤(1239/200 : ℝ)*82426 := by
  let E := Omitted 82426 c F
  have hEF : E⊆F := omitted_subset
  have hlegal : Legal (Ground 82426) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  exact PointArithmetic82426.actual_three_tenths_count hlegal omitted_bad (intermediate_dense g)


theorem strong {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    (L : ℝ) < (1/16 : ℝ)*82426 ∧ Width 82426 L R < (11/100 : ℝ)*82426 := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_lower (alpha := 1239/200) (beta := 0) (constant := 0) g
    (by simpa only [zero_mul, add_zero] using strong_omitted g)
  have hp' : RawProfile 82426 L (Width 82426 L R) (StrongA 0) (HLocal 0) 872 := by
    convert hp using 1 <;> norm_num [StrongA]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 14)
    (by decide : 14 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by
      have hl := (quarter g).1
      have hn : (0 : ℝ) ≤ 82426 := Nat.cast_nonneg 82426
      nlinarith only [hl, hn]) hp'
  exact Recovery208.actual_stage_bounds
    (by norm_num : (82426 : ℝ)≤82426) (PointArithmetic82426.strong_stage) hs

theorem strong_profile {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    Recovery208.WidthProfile L (Width 82426 L R) ≤
      StrongA 0*82426+BLocal 0 16*L+HLocal 0*Width 82426 L R+872 := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_lower (alpha := 1239/200) (beta := 0) (constant := 0) g
    (by simpa only [zero_mul, add_zero] using strong_omitted g)
  have hp' : RawProfile 82426 L (Width 82426 L R) (StrongA 0) (HLocal 0) 872 := by
    convert hp using 1 <;> norm_num [StrongA]
  exact local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 16)
    (by decide : 16 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using (strong g).1) hp'

theorem strong_dense {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ∀ S∈Omitted 82426 c F, (333/1000 : ℝ)*82426<S.card := by
  have hl := (strong g).1
  have hn : (0 : ℝ)≤82426 := Nat.cast_nonneg 82426
  intro S hS
  have hh := PointArithmetic82426.joint_omitter (1 : Fin 2) g
    (by nlinarith only [hl, hn])
    (by simpa [JointDensity82427.parameters] using strong_omitted g)
    (by simpa [JointDensity82427.parameters] using strong_profile g)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2
  simpa [JointDensity82427.parameters] using hh

theorem core {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hs := strong g
  have hn : (0 : ℝ) < 82426 := by exact_mod_cast (show 0 < 82426 by omega)
  have hi := RetainedIntervals86412.actual_avoiders_intervals g (by omega : 56400 ≤ 82426)
    (by omega : 82426 ≤ 88403)
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained 82426 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    82426 c L R (Retained 82426 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem prepared {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    ((Omitted 82426 c F).card : ℝ) ≤ (41/6 : ℝ)*Width 82426 L R-9/2 := by
  have hp := WeakFringe82427.preparation (by omega : 2000≤82426) (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g) (core g) (by simpa using (strong g).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem fine_profile {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    Recovery208.WidthProfile L (Width 82426 L R) ≤
      FineA 0*82426+BLocal 0 16*L+FineW 0*Width 82426 L R+FineC := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_lower (alpha := 0) (beta := 41/6) (constant := -9/2) g
    (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using prepared g)
  have hp' : RawProfile 82426 L (Width 82426 L R) (FineA 0) (FineW 0) FineC := by
    convert hp using 1 <;> norm_num [FineA, FineW, FineC]
  exact local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 16)
    (by decide : 16 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by
      have hl := (strong g).1
      have hn : (0 : ℝ) ≤ 82426 := Nat.cast_nonneg 82426
      nlinarith only [hl, hn]) hp'

theorem final_bounds {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    (L : ℝ) < (1/18 : ℝ)*82426 ∧ Width 82426 L R < (3/32 : ℝ)*82426 := by
  exact Recovery208.actual_stage_bounds
    (by norm_num : (82426 : ℝ)≤82426) (PointArithmetic82426.fine_final)
    (fine_profile g)

theorem native_profile {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    Recovery208.WidthProfile L (Width 82426 L R)≤FineA 0*82426+BLocal 0 18*L+FineW 0*Width 82426 L R+FineC := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide) (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_lower (alpha := 0) (beta := 41/6) (constant := -9/2) g
    (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using prepared g)
  have hp' : RawProfile 82426 L (Width 82426 L R) (FineA 0) (FineW 0) FineC := by
    convert hp using 1 <;> norm_num [FineA, FineW, FineC]
  exact local_profile hc (by have h:=g.root_left; omega) (by decide : 4≤18) (by decide : 18≤33)
    (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one]
      using (final_bounds g).1) hp'

theorem native_gates {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) :
    CoreSupply86412.Native 82426 L R := by
  have hs := final_bounds g
  let w := L+82426-R
  have hw : (w : ℝ)=Width 82426 L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by have hr := g.right_ground; omega : R≤L+82426)]
    push_cast
    ring
  have hwidth : 32*(L+82426-R)≤3*82426 := by
    have h : (32 : ℝ)*(w : ℝ)≤3*82426 := by rw [hw]; nlinarith only [hs.2]
    exact_mod_cast h
  exact PointArithmetic82426.native_from_profile g.right_ground hwidth
    (native_profile g)

#print axioms coarse_profile
#print axioms global_seventh
#print axioms coarse
#print axioms coarse_dense
#print axioms quarter_omitted
#print axioms quarter
#print axioms intermediate_dense
#print axioms strong_omitted
#print axioms strong
#print axioms strong_profile
#print axioms strong_dense
#print axioms core
#print axioms prepared
#print axioms fine_profile
#print axioms final_bounds
#print axioms native_profile
#print axioms native_gates
end
end JSP233.PointRecovery82426
