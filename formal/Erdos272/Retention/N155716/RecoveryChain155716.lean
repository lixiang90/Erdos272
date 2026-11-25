module

public import Erdos272.Resources.N158375.LocalRecovery158375
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Erdos272.Retention.N158375.RecoveryCertificates158375
public import Erdos272.Retention.N155716.DensityRecovery155716
public import Erdos272.Retention.N155716.FringePlans155716
public import Erdos272.Retention.N155716.RetainedIntervals155716

@[expose] public section

namespace JSP233.RecoveryChain155716
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open RecoveryParameters291012 (Lower)
open LocalRecovery158375 RecoveryCertificates158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem raw_profile_lower {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start N c L R F P T)
    (hN : 155716 ≤ N) (hhi : N ≤ 179999)
    (hE : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant) :
    RawProfile N L (Width N L R) (HLocal+433/100+alpha) (HLocal+beta) (872+constant) := by
  have hc := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
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

theorem coarse_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    RawProfile N L (Width N L R) CoarseA HLocal 2168 := by
  have he : ((Omitted N c F).card : ℝ) ≤ 144*N+1296 := by
    exact_mod_cast omitted_affine (by omega : 15853 ≤ N) g.legal
  have hp := raw_profile_lower (alpha := 144) (beta := 0) (constant := 1296) g hN hhi
    (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA]

theorem global_eighth {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    (L : ℝ) < (1/8 : ℝ)*N := by
  have hc := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hp := global_profile hc (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile g hN hhi)
  exact (Recovery208.actual_stage_bounds
    (show (155000 : ℝ) ≤ N by exact_mod_cast (show 155000 ≤ N by omega))
    RecoveryCertificates158375.global_eighth hp).1

theorem coarse {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    (L : ℝ) < (3/25 : ℝ)*N ∧ Width N L R < (49/250 : ℝ)*N := by
  have hc := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hp := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 8)
    (by decide : 8 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using global_eighth g hN hhi) (coarse_profile g hN hhi)
  exact Recovery208.actual_stage_bounds
    (show (155000 : ℝ) ≤ N by exact_mod_cast (show 155000 ≤ N by omega)) coarse_local hp

theorem coarse_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    ∀ S ∈ Omitted N c F, (1/4 : ℝ)*N < S.card := by
  have he : ((Omitted N c F).card : ℝ) ≤ 144*N+1296 := by
    exact_mod_cast omitted_affine (by omega : 15853 ≤ N) g.legal
  intro S hS
  exact DensityRecovery155716.actual_omitter_size g hN hhi (coarse g hN hhi).1 (coarse g hN hhi).2
    (by simpa only [zero_mul, add_zero] using he) DensityRecovery158375.quarter_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem strong_omitted {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    ((Omitted N c F).card : ℝ) ≤ 17*N := by
  let E := Omitted N c F
  have hEF : E ⊆ F := omitted_subset
  have hlegal : Legal (Ground N) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  have hbad : ∀ S ∈ E, ¬IsAP S := omitted_bad
  have hdense : ∀ S ∈ E, N < 4*S.card := by
    intro S hS
    have h := coarse_dense g hN hhi S hS
    have hd : (N : ℝ) < 4*S.card := by nlinarith only [h]
    exact_mod_cast hd
  have hb := DenseDeletion208.actual_dense_all_pair_budget (by decide : 0 < 4)
    (by omega : 4 < N) hlegal hbad hdense
  norm_num at hb
  have hn : (155000 : ℝ) ≤ N := by exact_mod_cast (show 155000 ≤ N by omega)
  have hp := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)-21 by linarith only [hn])
    (Nat.cast_nonneg (α := ℝ) N)
  have hpoly : 16*((N : ℝ)-1)*((N : ℝ)-2) ≤ 17*N*((N : ℝ)-4) := by
    nlinarith only [hp, hn]
  change (E.card : ℝ) ≤ 17*N
  by_contra hh
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh)
    (show (0 : ℝ) < (N : ℝ)-4 by linarith only [hn])
  nlinarith only [hb, hm, hpoly]

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    (L : ℝ) < (1/18 : ℝ)*N ∧ Width N L R < (1/10 : ℝ)*N := by
  have hc := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 17) (beta := 0) (constant := 0) g hN hhi
    (by simpa only [zero_mul, add_zero] using strong_omitted g hN hhi)
  have hp' : RawProfile N L (Width N L R) StrongA HLocal 872 := by
    convert hp using 1 <;> norm_num [StrongA]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 8)
    (by decide : 8 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using global_eighth g hN hhi) hp'
  exact Recovery208.actual_stage_bounds
    (show (155000 : ℝ) ≤ N by exact_mod_cast (show 155000 ≤ N by omega)) strong_eighteenth hs

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    ∀ S ∈ Omitted N c F, (1/3 : ℝ)*N < S.card := by
  intro S hS
  exact DensityRecovery155716.actual_omitter_size g hN hhi (strong g hN hhi).1 (strong g hN hhi).2
    (by simpa only [zero_mul, add_zero] using strong_omitted g hN hhi)
    DensityRecovery158375.third_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hs := strong g hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi := RetainedIntervals155716.actual_avoiders_intervals g hN hhi
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    ((Omitted N c F).card : ℝ) ≤ (13/2 : ℝ)*Width N L R-11/2 := by
  have hp := FringePlans155716.preparation hN (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (by simpa using (strong g hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 155716 ≤ N) (hhi : N ≤ 179999) :
    (L : ℝ) < (99/2500 : ℝ)*N ∧ Width N L R < (67/1000 : ℝ)*N := by
  have hc := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hp := raw_profile_lower (alpha := 0) (beta := 13/2) (constant := -11/2) g hN hhi
    (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using prepared g hN hhi)
  have hp' : RawProfile N L (Width N L R) FineA FineW FineC := by
    convert hp using 1 <;> norm_num [FineA, FineW, FineC]
  have hs := local_profile hc (by have h := g.root_left; omega) (by decide : 4 ≤ 18)
    (by decide : 18 ≤ 33) (by norm_num [BLocal, LogLocal, Lower, CovarianceScalar213.Polynomial])
    (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, mul_comm, one_mul, mul_one] using (strong g hN hhi).1) hp'
  exact Recovery208.actual_stage_bounds
    (show (155000 : ℝ) ≤ N by exact_mod_cast (show 155000 ≤ N by omega)) fine_final hs

#print axioms raw_profile_lower
#print axioms omitted_subset
#print axioms omitted_bad
#print axioms coarse_profile
#print axioms global_eighth
#print axioms coarse
#print axioms coarse_dense
#print axioms strong_omitted
#print axioms strong
#print axioms strong_dense
#print axioms core
#print axioms prepared
#print axioms final_bounds
end
end JSP233.RecoveryChain155716
