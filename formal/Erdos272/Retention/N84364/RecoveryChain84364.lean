module

public import Erdos272.Resources.N84364.LocalRecovery84364
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Erdos272.Counting.N86412.DenseCount86412
public import Erdos272.Retention.N84364.RecoveryCertificates84364
public import Erdos272.Retention.N84364.DensityRecovery84364
public import Erdos272.Counting.N84364.JointDensity84364
public import Erdos272.Retention.N109474.FringePlans109474
public import Erdos272.Retention.N86412.RetainedIntervals86412
public import Erdos272.Arithmetic.N84364.NativeGates84364

@[expose] public section

namespace JSP233.RecoveryChain84364
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery84364 RecoveryCertificates84364
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem raw_profile_lower {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start N c L R F P T)
    (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k)
    (hE : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant) :
    RawProfile N L (Width N L R) (HLocal k+433/100+alpha) (HLocal k+beta) (872+constant) := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hr := GenericRecovery291012.actual_original_raw_profile_local (by omega : 19 ≤ N)
    (by omega : N ≤ 720896) g.root_mem g.legal g.near_card g.root_left g.left_right
    g.right_ground g.root g.right_member g.right_avoids g.right_lower
    g.left_member g.left_avoids g.left_upper g.outside
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α := ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  change ((TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)).card : ℝ) ≤ _ at hE
  dsimp only [RawProfile, Coeff, Width, HLocal, CovarianceFamily214.MiddleCost,
    LocalRecovery208.GeometryCost] at *
  nlinarith only [hr, hE, hnpaid, hwpaid]

theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F ⊆ F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S ∈ Omitted N c F, ¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

theorem coarse_profile {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    RawProfile N L (Width N L R) (CoarseA k) (HLocal k) 872 := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have he : ((Omitted N c F).card : ℝ) ≤ 81*N := by
    exact_mod_cast DenseCount86412.actual_omitted_count (by omega : 56400 ≤ N)
      (by omega : N ≤ 2^18) g.legal
  have hp := raw_profile_lower (alpha := 81) (beta := 0) (constant := 0) g hk hN hhi
    (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA]

theorem global_eighth {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    (L : ℝ) < (1/8 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := global_profile hc (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile g hk hN hhi)
  exact (Recovery208.actual_stage_bounds
    (show (Low k : ℝ) ≤ N by exact_mod_cast hN)
    (RecoveryCertificates84364.global_eighth hk) hp).1

theorem coarse {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    (L : ℝ) < (49/400 : ℝ)*N ∧ Width N L R < (21/100 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 8)
    (by decide : 8 ≤ 33) (by interval_cases k <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using global_eighth g hk hN hhi) (coarse_profile g hk hN hhi)
  exact Recovery208.actual_stage_bounds
    (show (Low k : ℝ) ≤ N by exact_mod_cast hN) (coarse_local hk) hp

theorem coarse_dense {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ∀ S ∈ Omitted N c F, (1/4 : ℝ)*N < S.card := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have he : ((Omitted N c F).card : ℝ) ≤ 81*N := by
    exact_mod_cast DenseCount86412.actual_omitted_count (by omega : 56400 ≤ N)
      (by omega : N ≤ 2^18) g.legal
  intro S hS
  exact DensityRecovery84364.actual_omitter_size g hk hN hhi (coarse g hk hN hhi).1 (coarse g hk hN hhi).2
    (by simpa only [zero_mul, add_zero] using he) (DensityRecovery84364.quarter_gate hk) (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem quarter_omitted {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ((Omitted N c F).card : ℝ) ≤ (9 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  let E := Omitted N c F
  have hEF : E ⊆ F := omitted_subset
  have hlegal : Legal (Ground N) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  have hbad : ∀ S ∈ E, ¬IsAP S := omitted_bad
  have hdense : ∀ S ∈ E, (N : ℝ)/4 < S.card := by
    intro S hS
    have h := coarse_dense g hk hN hhi S hS
    nlinarith only [h]
  exact_mod_cast DenseCount86412.actual_quarter_count (by omega : 56400≤N)
    (by omega : N≤2^18) hlegal hbad hdense

theorem quarter {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    (L : ℝ) < (17/250 : ℝ)*N ∧ Width N L R < (14/125 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 9) (beta := 0) (constant := 0) g hk hN hhi
    (by simpa only [zero_mul, add_zero] using quarter_omitted g hk hN hhi)
  have hp' : RawProfile N L (Width N L R) (QuarterA k) (HLocal k) 872 := by
    convert hp using 1 <;> norm_num [QuarterA]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 8)
    (by decide : 8 ≤ 33) (by interval_cases k <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using global_eighth g hk hN hhi) hp'
  exact Recovery208.actual_stage_bounds
    (show (Low k : ℝ) ≤ N by exact_mod_cast hN) (quarter_stage hk) hs

theorem intermediate_dense {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ∀ S∈Omitted N c F, (3/10 : ℝ)*N<S.card := by
  have he := quarter_omitted g hk hN hhi
  intro S hS
  exact DensityRecovery84364.actual_omitter_size g hk hN hhi
    (quarter g hk hN hhi).1 (quarter g hk hN hhi).2
    (by simpa only [zero_mul, add_zero] using he) (DensityRecovery84364.intermediate_gate hk)
    (by norm_num) (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2


theorem strong_omitted {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ((Omitted N c F).card : ℝ)≤(25/4 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  let E := Omitted N c F
  have hEF : E⊆F := omitted_subset
  have hlegal : Legal (Ground N) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  exact DenseCount86412.actual_three_tenths_count (by omega : 56400≤N)
    (by omega : N≤2^18) hlegal omitted_bad (intermediate_dense g hk hN hhi)


theorem strong {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    (L : ℝ) < (1/16 : ℝ)*N ∧ Width N L R < (11/100 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 25/4) (beta := 0) (constant := 0) g hk hN hhi
    (by simpa only [zero_mul, add_zero] using strong_omitted g hk hN hhi)
  have hp' : RawProfile N L (Width N L R) (StrongA k) (HLocal k) 872 := by
    convert hp using 1 <;> norm_num [StrongA]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 14)
    (by decide : 14 ≤ 33) (by interval_cases k <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by
      have hl := (quarter g hk hN hhi).1
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith only [hl, hn]) hp'
  exact Recovery208.actual_stage_bounds
    (show (Low k : ℝ) ≤ N by exact_mod_cast hN) (strong_stage hk) hs

theorem strong_profile {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    Recovery208.WidthProfile L (Width N L R) ≤
      StrongA k*N+BLocal k 16*L+HLocal k*Width N L R+872 := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 25/4) (beta := 0) (constant := 0) g hk hN hhi
    (by simpa only [zero_mul, add_zero] using strong_omitted g hk hN hhi)
  have hp' : RawProfile N L (Width N L R) (StrongA k) (HLocal k) 872 := by
    convert hp using 1 <;> norm_num [StrongA]
  exact local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 16)
    (by decide : 16 ≤ 33) (by interval_cases k <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using (strong g hk hN hhi).1) hp'

theorem strong_dense {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ∀ S ∈ Omitted N c F, (1/3 : ℝ)*N < S.card := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  intro S hS
  exact JointDensity84364.actual_omitter_size g hk hN hhi (strong g hk hN hhi).1
    (strong_omitted g hk hN hhi) (strong_profile g hk hN hhi)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem core {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hs := strong g hk hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi := RetainedIntervals86412.actual_avoiders_intervals g (by omega : 56400 ≤ N)
    (by omega : N ≤ 88403)
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem prepared {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    ((Omitted N c F).card : ℝ) ≤ (13/2 : ℝ)*Width N L R-11/2 := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hp := FringePlans109474.preparation (by omega : 901 ≤ N) (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hk hN hhi) (core g hk hN hhi) (by simpa using (strong g hk hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem fine_profile {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    Recovery208.WidthProfile L (Width N L R) ≤
      FineA k*N+BLocal k 16*L+FineW k*Width N L R+FineC := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  have hc := LocalRecovery84364.actual_caps hk (by omega : 10000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 0) (beta := 13/2) (constant := -11/2) g hk hN hhi
    (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using prepared g hk hN hhi)
  have hp' : RawProfile N L (Width N L R) (FineA k) (FineW k) FineC := by
    convert hp using 1 <;> norm_num [FineA, FineW, FineC]
  exact local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 16)
    (by decide : 16 ≤ 33) (by interval_cases k <;> norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by
      have hl := (strong g hk hN hhi).1
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith only [hl, hn]) hp'

theorem final_bounds {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k ≤ N) (hhi : N ≤ High k) :
    (L : ℝ) < (27/500 : ℝ)*N ∧ Width N L R < (3/32 : ℝ)*N := by
  have hbase := (low_bound k).trans hN
  have htop := high_bound k
  exact Recovery208.actual_stage_bounds
    (show (Low k : ℝ) ≤ N by exact_mod_cast hN) (fine_final hk)
    (fine_profile g hk hN hhi)

theorem native_gates {N c L R k : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hk : k<1) (hN : Low k≤N) (hhi : N≤High k) :
    CoreSupply86412.Native N L R := by
  have hk0 : k=0 := by omega
  subst k
  have hbase := (low_bound 0).trans hN
  have hs := final_bounds g hk hN hhi
  let w := L+N-R
  have hw : (w : ℝ)=Width N L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by have hr := g.right_ground; omega : R≤L+N)]
    push_cast
    ring
  have hwidth : 32*(L+N-R)≤3*N := by
    have h : (32 : ℝ)*(w : ℝ)≤3*N := by rw [hw]; nlinarith only [hs.2]
    exact_mod_cast h
  exact NativeGates84364.native_from_profile hbase g.right_ground hwidth
    (fine_profile g hk hN hhi)

#print axioms raw_profile_lower
#print axioms omitted_subset
#print axioms omitted_bad
#print axioms coarse_profile
#print axioms global_eighth
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
#print axioms native_gates
end
end JSP233.RecoveryChain84364
