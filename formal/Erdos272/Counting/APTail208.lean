module

public import Erdos272.Counting.APCount41
public import Erdos272.Counting.EndpointExterior55
public import Erdos272.Counting.APProfile208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual APs of at least two points leave their common-root singleton
available in the endpoint rectangle. This removes the constant term for
every step, before summing the steps at least two. -/
namespace JSP233.APTail208
open StarCompletion APGeometry APCount41 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem singleton_apAt {d : ℕ} (hd : 0 < d) (c : ℤ) :
    APAt (d : ℤ) c ({c} : Finset ℤ) := by
  refine ⟨by exact_mod_cast hd, c, c, ?_⟩
  intro x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    subst x
    exact ⟨le_rfl, le_rfl, by simp⟩
  · intro hx
    omega

theorem legal_insert_common_singleton {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hroot : ∀ S ∈ F, c ∈ S) :
    Legal (Ground N) (insert ({c} : Finset ℤ) F) := by
  constructor
  · intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact Finset.singleton_subset_iff.mpr hc
    · exact hlegal.1 S hS
  · intro S hS T hT hST
    rcases Finset.mem_insert.mp hS with rfl | hS
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · exact False.elim (hST rfl)
      · have he : ({c} : Finset ℤ) ∩ T = {c} := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · exact fun h => h.1
          · intro hz
            exact ⟨hz, hz ▸ hroot T hT⟩
        rw [he]
        exact singleton_isAP c
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · have he : S ∩ ({c} : Finset ℤ) = {c} := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · intro hz
            exact ⟨hz ▸ hroot S hS, hz⟩
        rw [he]
        exact singleton_isAP c
      · exact hlegal.2 S hS T hT hST

theorem actual_same_step_two_count {N d : ℕ} {F : Finset (Finset ℤ)}
    (hd : 0 < d) (hlegal : Legal (Ground N) F)
    (htwo : ∀ S ∈ F, 2 ≤ S.card)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APAt (d : ℤ) p S) :
    (F.card : ℝ) ≤ (N : ℝ)^2 / (4 * (d : ℝ)^2) + (N : ℝ) / d := by
  by_cases hF : F.Nonempty
  · have hne : ∀ S ∈ F, S.Nonempty := fun S hS =>
      Finset.card_pos.mp (by have ht := htwo S hS; omega)
    obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root hF hlegal hne hstep
    have hnot : ({c} : Finset ℤ) ∉ F := by
      intro hmem
      have ht := htwo {c} hmem
      simp only [Finset.card_singleton] at ht
      omega
    let G := insert ({c} : Finset ℤ) F
    have hG : Legal (Ground N) G := legal_insert_common_singleton hc hlegal hroot
    have hGne : ∀ S ∈ G, S.Nonempty := by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact Finset.singleton_nonempty c
      · exact hne S hS
    have hGstep : ∀ S ∈ G, ∃ p : ℤ, APAt (d : ℤ) p S := by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact ⟨c, singleton_apAt hd c⟩
      · exact hstep S hS
    have hb := actual_same_step_count hd hG hGne hGstep
    have he : (G.card : ℝ) = (F.card : ℝ) + 1 := by
      dsimp only [G]
      rw [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    rw [he] at hb
    linarith only [hb]
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity

theorem harmonic_tail_two {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / d) = Harmonic N - 1 := by
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  dsimp only [Harmonic]
  rw [hsplit, Finset.sum_insert (by simp)]
  norm_num

theorem actual_large_step_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (htwo : ∀ S ∈ F, 2 ≤ S.card)
    (hlarge : ∀ S ∈ F, 2 ≤ Step S) :
    (F.card : ℝ) ≤ (129 / 800 : ℝ) * N^2 + (N : ℝ) * (Harmonic N - 1) := by
  have hmaps : ∀ S ∈ F, Step S ∈ Finset.Icc 2 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨hlarge S hS,
      actual_step_bound (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card : ℝ) =
      ∑ d ∈ Finset.Icc 2 N, ((F.filter (fun S => Step S = d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ d ∈ Finset.Icc 2 N,
      ((F.filter (fun S => Step S = d)).card : ℝ) ≤
        (N : ℝ)^2 / (4 * (d : ℝ)^2) + (N : ℝ) / d := by
    intro d hd
    have hsub : F.filter (fun S => Step S = d) ⊆ F := Finset.filter_subset _ _
    have hC : Legal (Ground N) (F.filter (fun S => Step S = d)) :=
      ⟨fun S hS => hlegal.1 S (hsub hS),
       fun S hS T hT hST => hlegal.2 S (hsub hS) T (hsub hT) hST⟩
    apply actual_same_step_two_count (by have hh := (Finset.mem_Icc.mp hd).1; omega)
      hC (fun S hS => htwo S (hsub hS))
    intro S hS
    obtain ⟨_, p, hp⟩ := actual_step (hAP S (hsub hS))
    exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2] using hp⟩
  have hsum : (F.card : ℝ) ≤
      (N : ℝ)^2 / 4 * (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ)^2) +
      (N : ℝ) * (Harmonic N - 1) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 N,
          ((N : ℝ)^2 / (4 * (d : ℝ)^2) + (N : ℝ) / d) := by
        rw [hpart]
        exact Finset.sum_le_sum hclass
      _ = _ := by
        have hterm : ∀ d : ℕ,
            (N : ℝ)^2 / (4 * (d : ℝ)^2) + (N : ℝ) / d =
              (N : ℝ)^2 / 4 * (1 / (d : ℝ)^2) + (N : ℝ) * (1 / d) := by
          intro d
          ring
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          harmonic_tail_two hN]
  have hquad := mul_le_mul_of_nonneg_left (EndpointExterior55.reciprocal_square_tail_two N)
    (show (0 : ℝ) ≤ (N : ℝ)^2 / 4 by positivity)
  nlinarith only [hsum, hquad]

theorem actual_AP_profile_sharp {N a : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (haN : a ≤ N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (hmax : ∀ S ∈ F, S.card ≤ a) :
    (F.card : ℝ) ≤
      (APCoupling208.APCoefficient ((a : ℝ) / N) + 129 / 800) * N^2 +
      (N : ℝ) * Harmonic N + 1 := by
  let A := F.filter fun S => 2 ≤ S.card
  let C := F.filter fun S => ¬ 2 ≤ S.card
  let U := A.filter fun S => Step S = 1
  let D := A.filter fun S => ¬ Step S = 1
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hUA : U ⊆ A := Finset.filter_subset _ _
  have hDA : D ⊆ A := Finset.filter_subset _ _
  have hUF : U ⊆ F := hUA.trans hAF
  have hDF : D ⊆ F := hDA.trans hAF
  have hsublegal : ∀ G : Finset (Finset ℤ), G ⊆ F → Legal (Ground N) G := by
    intro G hGF
    exact ⟨fun S hS => hlegal.1 S (hGF hS),
      fun S hS T hT hST => hlegal.2 S (hGF hS) T (hGF hT) hST⟩
  have hunit := APProfile208.actual_unit_step_profile hN haN (hsublegal U hUF)
    (fun S hS => isAP_nonempty (hAP S (hUF hS)))
    (fun S hS => ⟨(Finset.mem_filter.mp (hUA hS)).2, hmax S (hUF hS)⟩)
    (fun S hS => by
      obtain ⟨_, p, hp⟩ := actual_step (hAP S (hUF hS))
      exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2, Nat.cast_one] using hp⟩)
  have htail := actual_large_step_count hN (hsublegal D hDF)
    (fun S hS => hAP S (hDF hS))
    (fun S hS => (Finset.mem_filter.mp (hDA hS)).2)
    (fun S hS => by
      have hp := (actual_step (hAP S (hDF hS))).1
      have hn := (Finset.mem_filter.mp hS).2
      omega)
  have hsmall := actual_singleton_family_count (hsublegal C hCF)
    (fun S hS => by have hn := (Finset.mem_filter.mp hS).2; omega)
  have hpart := Finset.card_filter_add_card_filter_not (s := F) (fun S => 2 ≤ S.card)
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun S => Step S = 1)
  change A.card + C.card = F.card at hpart
  change U.card + D.card = A.card at hsplit
  have hpartR : (A.card : ℝ) + C.card = F.card := by exact_mod_cast hpart
  have hsplitR : (U.card : ℝ) + D.card = A.card := by exact_mod_cast hsplit
  have hsmallR : (C.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
  nlinarith only [hunit, htail, hpartR, hsplitR, hsmallR]

theorem actual_AP_profile {N a : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (haN : a ≤ N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (hmax : ∀ S ∈ F, S.card ≤ a) :
    (F.card : ℝ) ≤
      (APCoupling208.APCoefficient ((a : ℝ) / N) + 129 / 800) * N^2 +
      (Harmonic N + 1) * N + 1 := by
  have hp := actual_AP_profile_sharp hN haN hlegal hAP hmax
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith only [hp, hN0]

theorem actual_AP_profile_of_maximum {N : ℕ} {F : Finset (Finset ℤ)}
    {A : Finset ℤ} (hN : 1 ≤ N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (hA : A ∈ F) (hmax : ∀ S ∈ F, S.card ≤ A.card) :
    (F.card : ℝ) ≤
      (APCoupling208.APCoefficient ((A.card : ℝ) / N) + 129 / 800) * N^2 +
      (N : ℝ) * Harmonic N + 1 := by
  have hAN : A.card ≤ N := by
    simpa only [ground_card] using Finset.card_le_card (hlegal.1 A hA)
  exact actual_AP_profile_sharp hN hAN hlegal hAP hmax

theorem actual_AP_members_profile {N : ℕ} {F : Finset (Finset ℤ)}
    {A : Finset ℤ} (hN : 1 ≤ N) (hlegal : Legal (Ground N) F)
    (hA : A ∈ F) (hAA : IsAP A)
    (hmax : ∀ S ∈ F, IsAP S → S.card ≤ A.card) :
    ((F.filter IsAP).card : ℝ) ≤
      (APCoupling208.APCoefficient ((A.card : ℝ) / N) + 129 / 800) * N^2 +
      (N : ℝ) * Harmonic N + 1 := by
  have hsub : F.filter IsAP ⊆ F := Finset.filter_subset _ _
  have hG : Legal (Ground N) (F.filter IsAP) :=
    ⟨fun S hS => hlegal.1 S (hsub hS),
     fun S hS T hT hST => hlegal.2 S (hsub hS) T (hsub hT) hST⟩
  exact actual_AP_profile_of_maximum hN hG
    (fun S hS => (Finset.mem_filter.mp hS).2) (Finset.mem_filter.mpr ⟨hA, hAA⟩)
    (fun S hS => hmax S (hsub hS) (Finset.mem_filter.mp hS).2)

#print axioms singleton_apAt
#print axioms legal_insert_common_singleton
#print axioms actual_same_step_two_count
#print axioms harmonic_tail_two
#print axioms actual_large_step_count
#print axioms actual_AP_profile_sharp
#print axioms actual_AP_profile
#print axioms actual_AP_profile_of_maximum
#print axioms actual_AP_members_profile
end
end JSP233.APTail208
