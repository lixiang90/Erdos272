module

public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Erdos272.Retention.N190000.RecoveryProfiles190000
public import Erdos272.Retention.N190000.DensityRecovery190000
public import Erdos272.Retention.N190000.FringePlans190000
public import Erdos272.Retention.N190000.RetainedIntervals190000

@[expose] public section

namespace JSP233.RecoveryChain190000
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 RecoveryParameters291012 RecoveryProfiles190000 WitnessInterval43
open RecoveryCertificates190000
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000


theorem raw_profile_lower {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start N c L R F P T)
    (hN : 190000 ≤ N) (hhi : N ≤ 199999)
    (hE : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant) :
    RawProfile N L (Width N L R) (HLocal+433/100+alpha) (HLocal+beta) (872+constant) := by
  have hc := LowResourceBridges3040.local_caps (by omega : 100000 ≤ N) (by omega : N ≤ 291011)
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

#print axioms raw_profile_lower

theorem coarse_profile_local {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999)
    : RawProfile N L (Width N L R) CoarseA190000 HLocal 2168 := by
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (by omega : 15853 ≤ N) g.legal
  have hp := raw_profile_lower (alpha := 144) (beta := 0) (constant := 1296) g
    hN hhi (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA190000, HCap, LogCap, HLocal, CoarseA190000, StrongA190000, FineA190000]


theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F ⊆ F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S ∈ Omitted N c F, ¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

theorem coarse {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    (L : ℝ) < (N : ℝ)/9 ∧ Width N L R < (1/5 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hs := RecoveryProfiles190000.coarse_bounds hN caps (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile_local g hN hhi)
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

theorem coarse_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ∀ S ∈ Omitted N c F, (1/6 : ℝ)*(N : ℝ) < S.card := by
  have hw := (coarse g hN hhi).2
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (c := c) (by omega : 15853 ≤ N) g.legal
  intro S hS
  exact DensityRecovery190000.actual_omitter_size g hN (by omega : N ≤ 642498)
    (by nlinarith only [hw]) (by simpa only [zero_mul, add_zero] using he) DensityRecovery190000.coarse_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem strong_omitted {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ((Omitted N c F).card : ℝ) ≤ (3601/100 : ℝ)*N := by
  let E := Omitted N c F
  have hEF : E ⊆ F := omitted_subset
  have hlegal : Legal (Ground N) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS), fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  have hbad : ∀ S ∈ E, ¬IsAP S := omitted_bad
  have hdense : ∀ S ∈ E, N < 6*S.card := by
    intro S hS
    have h := coarse_dense g hN hhi S hS
    have hd : (N : ℝ) < 6*S.card := by nlinarith only [h]
    exact_mod_cast hd
  have hb := DenseDeletion208.actual_dense_all_pair_budget (by decide : 0 < 6)
    (by omega : 6 < N) hlegal hbad hdense
  norm_num at hb
  have hn : (190000 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)-10807 by linarith only [hn])
    (Nat.cast_nonneg (α := ℝ) N)
  have hpoly : 36*((N : ℝ)-1)*((N : ℝ)-2) ≤ (3601/100 : ℝ)*N*((N : ℝ)-6) := by
    nlinarith only [hp, hn]
  change (E.card : ℝ) ≤ (3601/100 : ℝ)*N
  by_contra hh
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh) (show (0 : ℝ) < (N : ℝ)-6 by linarith only [hn])
  nlinarith only [hb, hm, hpoly]

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    (L : ℝ) < (N : ℝ)/16 ∧ Width N L R < (52/500 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := strong_omitted g hN hhi
  have hp := raw_profile_lower (alpha := 3601/100) (beta := 0) (constant := 0) g
    hN hhi (by simpa only [zero_mul, add_zero] using he)
  have hp' : RawProfile N L (Width N L R) StrongA190000 HLocal 872 := by
    convert hp using 1 <;> norm_num [StrongA190000, HCap, LogCap, HLocal, CoarseA190000, StrongA190000, FineA190000]
  exact RecoveryProfiles190000.strong_bounds hN caps (by have h := g.root_left; omega) (coarse g hN hhi).1 hp'

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ∀ S ∈ Omitted N c F, (189/1000 : ℝ)*(N : ℝ) < S.card := by
  have hw := (strong g hN hhi).2
  have he := strong_omitted g hN hhi
  intro S hS
  exact DensityRecovery190000.actual_omitter_size g hN (by omega : N ≤ 642498) hw
    (by simpa only [zero_mul, add_zero] using he) DensityRecovery190000.strong_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hs := strong g hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi := RetainedIntervals190000.actual_avoiders_intervals g hN (by omega : N ≤ 642498)
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem first_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ((Omitted N c F).card : ℝ) ≤ (1337/60 : ℝ)*Width N L R-297/20 := by
  have hp := FringePlans190000.prep1 hN (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (by simpa using (strong g hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem intermediate_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    (L : ℝ) < (N : ℝ)/26 ∧ Width N L R < (1/15 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := first_prepared g hN hhi
  have hp := raw_profile_lower (alpha := 0) (beta := 1337/60) (constant := -297/20) g
    hN hhi (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using he)
  have hp' : RawProfile N L (Width N L R) FineA190000 FineW190000 FineC190000 := by
    convert hp using 1 <;> norm_num [FineA190000, FineW190000, FineC190000, HCap, LogCap, HLocal, CoarseA190000, StrongA190000, FineA190000]
  exact RecoveryProfiles190000.fine_bounds hN caps (by have h := g.root_left; omega) (strong g hN hhi).1 hp'


theorem second_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    ((Omitted N c F).card : ℝ) ≤ (947/60 : ℝ)*Width N L R-187/20 := by
  have hp := FringePlans190000.rank6 hN (by have hh := g.root_left; omega) g.left_right
    g.right_ground g.legal omitted_subset omitted_bad (strong_dense g hN hhi)
    (core g hN hhi) (intermediate_bounds g hN hhi).2
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 190000 ≤ N) (hhi : N ≤ 199999) :
    (L : ℝ) < (N : ℝ)/26 ∧ Width N L R < (1/16 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hp := raw_profile_lower (alpha := 0) (beta := 947/60) (constant := -187/20) g
    hN hhi (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using second_prepared g hN hhi)
  have hp' : RawProfile N L (Width N L R) FineA190000 SecondW190000 SecondC190000 := by
    convert hp using 1 <;> norm_num [FineA190000, SecondW190000, SecondC190000, HCap, LogCap, HLocal, CoarseA190000, StrongA190000, FineA190000]
  have profile := local_profile caps (by have hh := g.root_left; omega)
    (by decide : 4 ≤ 26) (by decide : 26 ≤ 33) (intermediate_bounds g hN hhi).1 hp'
  have hn : (190000 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := Recovery208.actual_stage_bounds hn second_width profile
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

#print axioms second_prepared
#print axioms final_bounds


#print axioms coarse_profile_local
#print axioms omitted_subset
#print axioms omitted_bad
#print axioms coarse
#print axioms coarse_dense
#print axioms strong_omitted
#print axioms strong
#print axioms strong_dense
#print axioms core
#print axioms first_prepared
#print axioms intermediate_bounds
end
end JSP233.RecoveryChain190000
