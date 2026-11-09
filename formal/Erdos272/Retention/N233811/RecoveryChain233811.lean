module

public import Erdos272.Retention.N233811.RecoveryProfiles233811
public import Erdos272.Retention.N233811.DensityRecovery233811
public import Erdos272.Retention.N233811.FringePlans233811
public import Erdos272.Retention.N233811.RetainedIntervals233811
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.RecoveryChain233811
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 RecoveryParameters291012 RecoveryProfiles233811 RecoveryCertificates250262 WitnessInterval43
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem coarse_profile_local {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498)
    (hc : Caps LogCap HCap N) : RawProfile N L (Width N L R) CoarseA HCap 2168 := by
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (by omega : 15853 ≤ N) g.legal
  have hp := raw_profile (alpha := 144) (beta := 0) (constant := 1296) g
    (by omega : 19 ≤ N) hhi hc (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA, HCap, LogCap]


theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F ⊆ F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S ∈ Omitted N c F, ¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

theorem coarse {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/10 ∧ Width N L R < (N : ℝ)/6 := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hs := RecoveryProfiles233811.coarse_bounds hN caps (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile_local g hN hhi caps)
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

theorem coarse_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    ∀ S ∈ Omitted N c F, (1/6 : ℝ)*(N : ℝ) < S.card := by
  have hw := (coarse g hN hhi).2
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (c := c) (by omega : 15853 ≤ N) g.legal
  intro S hS
  exact DensityRecovery233811.actual_omitter_size g hN hhi
    (by nlinarith only [hw]) (by simpa only [zero_mul, add_zero] using he) DensityRecovery233811.coarse_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem strong_omitted {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
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
  have hn : (233811 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)-10807 by linarith only [hn])
    (Nat.cast_nonneg (α := ℝ) N)
  have hpoly : 36*((N : ℝ)-1)*((N : ℝ)-2) ≤ (3601/100 : ℝ)*N*((N : ℝ)-6) := by
    nlinarith only [hp, hn]
  change (E.card : ℝ) ≤ (3601/100 : ℝ)*N
  by_contra hh
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh) (show (0 : ℝ) < (N : ℝ)-6 by linarith only [hn])
  nlinarith only [hb, hm, hpoly]

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/17 ∧ Width N L R < (2/21 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := strong_omitted g hN hhi
  have hp := raw_profile (alpha := 3601/100) (beta := 0) (constant := 0) g
    (by omega : 19 ≤ N) hhi caps (by simpa only [zero_mul, add_zero] using he)
  have hp' : RawProfile N L (Width N L R) StrongA HCap 872 := by
    convert hp using 1 <;> norm_num [StrongA, HCap, LogCap]
  exact RecoveryProfiles233811.strong_bounds hN caps (by have h := g.root_left; omega) (coarse g hN hhi).1 hp'

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    ∀ S ∈ Omitted N c F, (19/100 : ℝ)*(N : ℝ) < S.card := by
  have hw := (strong g hN hhi).2
  have he := strong_omitted g hN hhi
  intro S hS
  exact DensityRecovery233811.actual_omitter_size g hN hhi hw
    (by simpa only [zero_mul, add_zero] using he) DensityRecovery233811.strong_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hs := strong g hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi := RetainedIntervals233811.actual_avoiders_intervals g hN hhi
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem first_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    ((Omitted N c F).card : ℝ) ≤ (1217/60 : ℝ)*Width N L R-257/20 := by
  have hp := FringePlans233811.prep1 hN (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (by simpa using (strong g hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 233811 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/29 ∧ Width N L R < (1/17 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := first_prepared g hN hhi
  have hp := raw_profile (alpha := 0) (beta := 1217/60) (constant := -257/20) g
    (by omega : 19 ≤ N) hhi caps (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using he)
  have hp' : RawProfile N L (Width N L R) FineA FineW250262 FineC250262 := by
    convert hp using 1 <;> norm_num [FineA, FineW250262, FineC250262, HCap, LogCap]
  exact RecoveryProfiles233811.fine_bounds hN caps (by have h := g.root_left; omega) (strong g hN hhi).1 hp'


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
#print axioms final_bounds
end
end JSP233.RecoveryChain233811
