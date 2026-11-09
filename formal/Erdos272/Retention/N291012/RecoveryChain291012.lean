module

public import Erdos272.Retention.N291012.DensityRecovery291012
public import Erdos272.Retention.N291012.FringePlans291012
public import Erdos272.Retention.N291012.RetainedIntervals291012
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.RecoveryChain291012
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 RecoveryParameters291012 WitnessInterval43
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem omitted_subset {N c : ℕ} {F : Finset (Finset ℤ)} : Omitted N c F ⊆ F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)

theorem omitted_bad {N c : ℕ} {F : Finset (Finset ℤ)} : ∀ S ∈ Omitted N c F, ¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

theorem coarse {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/11 ∧ Width N L R < (N : ℝ)/7 := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  exact coarse_bounds hN caps (by have h := g.root_left; omega)
    (g.left_right.trans g.right_ground) (coarse_profile g hN hhi caps)

theorem coarse_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ∀ S ∈ Omitted N c F, (1/6 : ℝ)*(N : ℝ) < S.card := by
  have hw := (coarse g hN hhi).2
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (c := c) (by omega : 15853 ≤ N) g.legal
  intro S hS
  exact DensityRecovery291012.actual_omitter_size g hN hhi
    (by nlinarith only [hw]) (by simpa only [zero_mul, add_zero] using he) DensityRecovery291012.coarse_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem strong_omitted {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
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
  have hn : (291012 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)-10807 by linarith only [hn])
    (Nat.cast_nonneg (α := ℝ) N)
  have hpoly : 36*((N : ℝ)-1)*((N : ℝ)-2) ≤ (3601/100 : ℝ)*N*((N : ℝ)-6) := by
    nlinarith only [hp, hn]
  change (E.card : ℝ) ≤ (3601/100 : ℝ)*N
  by_contra hh
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hh) (show (0 : ℝ) < (N : ℝ)-6 by linarith only [hn])
  nlinarith only [hb, hm, hpoly]

theorem strong {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/20 ∧ Width N L R < (4/47 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := strong_omitted g hN hhi
  have hp := raw_profile (alpha := 3601/100) (beta := 0) (constant := 0) g
    (by omega : 19 ≤ N) hhi caps (by simpa only [zero_mul, add_zero] using he)
  have hp' : RawProfile N L (Width N L R) StrongA HCap 872 := by
    convert hp using 1 <;> norm_num [StrongA, HCap, LogCap]
  exact strong_bounds hN caps (by have h := g.root_left; omega) (coarse g hN hhi).1 hp'

theorem strong_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ∀ S ∈ Omitted N c F, (19/100 : ℝ)*(N : ℝ) < S.card := by
  have hw := (strong g hN hhi).2
  have he := strong_omitted g hN hhi
  intro S hS
  exact DensityRecovery291012.actual_omitter_size g hN hhi hw
    (by simpa only [zero_mul, add_zero] using he) DensityRecovery291012.strong_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hs := strong g hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi := RetainedIntervals291012.actual_avoiders_intervals g hN hhi
    (by nlinarith only [hs.1, hn])
  have hne : (Avoiders (Retained N 12 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  obtain ⟨H, hHG, hHAP, hIH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 12 F) g.left_right hne hi
  exact ⟨H, (Finset.mem_sdiff.mp hHG).1, hHAP, hIH⟩

theorem first_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ((Omitted N c F).card : ℝ) ≤ (1097/60 : ℝ)*Width N L R-217/20 := by
  have hp := FringePlans291012.prep1 hN (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (strong_dense g hN hhi) (core g hN hhi) (by simpa using (strong g hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem fine1 {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/33 ∧ Width N L R < (2/39 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := first_prepared g hN hhi
  have hp := raw_profile (alpha := 0) (beta := 1097/60) (constant := -217/20) g
    (by omega : 19 ≤ N) hhi caps (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using he)
  have hp' : RawProfile N L (Width N L R) FineA FineW1 FineC1 := by
    convert hp using 1 <;> norm_num [FineA, FineW1, FineC1, HCap, LogCap]
  exact fine1_bounds hN caps (by have h := g.root_left; omega) (strong g hN hhi).1 hp'

theorem fine_dense {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ∀ S ∈ Omitted N c F, (39/200 : ℝ)*(N : ℝ) < S.card := by
  have hw := (fine1 g hN hhi).2
  have he := first_prepared g hN hhi
  intro S hS
  exact DensityRecovery291012.actual_omitter_size g hN hhi hw
    (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using he) DensityRecovery291012.fine_gate (by norm_num)
    (omitted_subset hS) (omitted_bad S hS) (Finset.mem_filter.mp hS).2

theorem second_prepared {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    ((Omitted N c F).card : ℝ) ≤ (827/60 : ℝ)*Width N L R-147/20 := by
  have hp := FringePlans291012.prep2 hN (by have h := g.root_left; omega)
    g.left_right g.right_ground g.legal omitted_subset omitted_bad
    (fine_dense g hN hhi) (core g hN hhi) (by simpa using (fine1 g hN hhi).2)
  simpa only [sub_eq_add_neg, neg_div] using hp

theorem final_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498) :
    (L : ℝ) < (N : ℝ)/33 ∧ Width N L R < (4/79 : ℝ)*(N : ℝ) := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have he := second_prepared g hN hhi
  have hp := raw_profile (alpha := 0) (beta := 827/60) (constant := -147/20) g
    (by omega : 19 ≤ N) hhi caps (by simpa only [zero_mul, zero_add, sub_eq_add_neg, neg_div] using he)
  have hp' : RawProfile N L (Width N L R) FineA FineW2 FineC2 := by
    convert hp using 1 <;> norm_num [FineA, FineW2, FineC2, HCap, LogCap]
  exact fine2_bounds hN caps (by have h := g.root_left; omega) (fine1 g hN hhi).1 hp'

#print axioms omitted_subset
#print axioms omitted_bad
#print axioms coarse
#print axioms coarse_dense
#print axioms strong_omitted
#print axioms strong
#print axioms strong_dense
#print axioms core
#print axioms first_prepared
#print axioms fine1
#print axioms fine_dense
#print axioms second_prepared
#print axioms final_bounds
end
end JSP233.RecoveryChain291012
