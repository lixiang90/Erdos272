module

public import Erdos272.Counting.EndpointExterior55
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual exterior progressions retain their two physical fringe lengths.
The linear error is paid by their sum w instead of being replaced by 2N. -/
namespace JSP233.ActualExterior208
open StarCompletion APGeometry HarmonicAbel29
open APCount41 APExterior50 APPrepare49 PreparedClasses50 PreparedWitness48
open RestrictedWitness44 MiddleCoordinates51
open LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Keep both real fringe lengths in the actual endpoint rectangle. -/
theorem actual_same_step_endpoint_width {N L R d : ℕ} {F : Finset (Finset ℤ)}
    (hRN : R ≤ N) (hF : Legal (Ground N) F)
    (hne : ∀ S ∈ F, S.Nonempty)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APAt (d : ℤ) p S)
    (hends : ∀ S ∈ F, Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S) :
    (F.card : ℝ) ≤ (L : ℝ) * (N - R) / (d : ℝ)^2 +
      ((L : ℝ) + (N - R)) / d + 1 := by
  have hr := APExterior50.actual_same_step_endpoint_rectangle hF hne hstep hends
  have hrR : (F.card : ℝ) ≤ ((L / d : ℕ) + 1 : ℝ) *
      (((N - R) / d : ℕ) + 1 : ℝ) := by exact_mod_cast hr
  have hleft := Nat.cast_div_le (α := ℝ) (m := L) (n := d)
  have hright := Nat.cast_div_le (α := ℝ) (m := N - R) (n := d)
  rw [Nat.cast_sub hRN] at hright
  have hp : (F.card : ℝ) ≤ ((L : ℝ) / d + 1) * (((N : ℝ) - R) / d + 1) :=
    hrR.trans (mul_le_mul (by linarith only [hleft]) (by linarith only [hright])
      (by positivity) (by positivity))
  calc
    _ ≤ _ := hp
    _ = _ := by ring

theorem actual_large_step_endpoint_width {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hRN : R ≤ N) (hF : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (htwo : ∀ S ∈ F, 2 ≤ S.card)
    (hlarge : ∀ S ∈ F, 2 ≤ Step S)
    (hends : ∀ S ∈ F, Low S ≤ (L : ℤ) ∧ (R : ℤ) ≤ High S) :
    (F.card : ℝ) ≤ (129 / 200 : ℝ) * L * (N - R) +
      ((L : ℝ) + (N - R)) * Harmonic N + N := by
  have hmaps : Set.MapsTo Step (F : Set (Finset ℤ)) (Finset.Icc 2 N) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨hlarge S hS,
      actual_step_bound (hF.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card : ℝ) =
      ∑ d ∈ Finset.Icc 2 N, ((F.filter (fun S => Step S = d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ d ∈ Finset.Icc 2 N,
      ((F.filter (fun S => Step S = d)).card : ℝ) ≤
        (L : ℝ) * (N - R) / (d : ℝ)^2 + ((L : ℝ) + (N - R)) / d + 1 := by
    intro d _hd
    have hsub : F.filter (fun S => Step S = d) ⊆ F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) (F.filter (fun S => Step S = d)) :=
      ⟨fun S hS => hF.1 S (hsub hS),
       fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
    apply actual_same_step_endpoint_width hRN hlegal
      (fun S hS => isAP_nonempty (hAP S (hsub hS)))
    · intro S hS
      obtain ⟨hSF, hSd⟩ := Finset.mem_filter.mp hS
      obtain ⟨_, p, hp⟩ := actual_step (hAP S hSF)
      exact ⟨p, by simpa only [hSd] using hp⟩
    · exact fun S hS => hends S (hsub hS)
  have hinv : (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹) ≤ Harmonic N := by
    simp only [Harmonic, one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hd, hdN⟩ := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega, hdN⟩
    · intro d _ _
      positivity
  have hcardI : ((Finset.Icc 2 N).card : ℝ) ≤ N := by
    exact_mod_cast (show (Finset.Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
  have hsum : (F.card : ℝ) ≤
      (L : ℝ) * (N - R) * (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ)^2) +
      ((L : ℝ) + (N - R)) * (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹) +
      (Finset.Icc 2 N).card := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 N,
          ((L : ℝ) * (N - R) / (d : ℝ)^2 + ((L : ℝ) + (N - R)) / d + 1) := by
        rw [hpart]
        exact Finset.sum_le_sum hbound
      _ = _ := by
        simp only [div_eq_mul_inv, one_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hRN' : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hquad := mul_le_mul_of_nonneg_left (EndpointExterior55.reciprocal_square_tail_two N)
    (show (0 : ℝ) ≤ (L : ℝ) * (N - R) by positivity)
  have hharm := mul_le_mul_of_nonneg_left hinv
    (show (0 : ℝ) ≤ (L : ℝ) + (N - R) by positivity)
  linarith only [hsum, hquad, hharm, hcardI]

theorem actual_prepared_EX_width {N c L R : ℕ} {G : Finset (Finset ℤ)}
    {P : Finset ℤ} (hG : Legal (Ground N) G) (hcL : c < L)
    (hRN : R ≤ N) (hP : P ∈ G) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (houtside : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    ((EX (PreparedAP G c L) R).card : ℝ) ≤
      (129 / 200 : ℝ) * L * (N - R) + ((L : ℝ) + (N - R)) * Harmonic N + N := by
  have hm := fun S hS => actual_EX_endpoints hG hcL hP hLP houtside (S := S) hS
  have hsub : EX (PreparedAP G c L) R ⊆ G := fun S hS => (hm S hS).1
  have hlegal : Legal (Ground N) (EX (PreparedAP G c L) R) :=
    ⟨fun S hS => hG.1 S (hsub hS),
     fun S hS T hT hST => hG.2 S (hsub hS) T (hsub hT) hST⟩
  apply actual_large_step_endpoint_width hRN hlegal
    (fun S hS => (hm S hS).2.1)
  · intro S hS
    have hh := (hm S hS).2.2.1
    omega
  · exact fun S hS => (hm S hS).2.2.2.1
  · exact fun S hS => (hm S hS).2.2.2.2

theorem actual_prepared_middle_reduction_width {N c L R : ℕ}
    {G : Finset (Finset ℤ)} {P : Finset ℤ} (x p : Finset ℤ → ℤ)
    (hG : Legal (Ground N) G) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hP : P ∈ G) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S)
    (houtside : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    (hW : ∀ S ∈ PreparedCrooked G c L,
      IntrinsicPair c S {x S, p S} ∧ x S ≤ (R : ℤ) ∧ x S ≠ (L : ℤ) ∧
      ((c : ℤ) < x S → x S < (L : ℤ) → (R : ℤ) < p S →
        S ∩ Finset.Icc (x S) (p S) = {x S, p S} ∨
          ¬ IsAP (S ∩ Finset.Icc (x S) (p S)))) :
    ((PreparedCrooked G c L).card : ℝ) + (PreparedAP G c L).card ≤
      (CM (PreparedCrooked G c L) p R).card + (EM (PreparedAP G c L) c R).card +
      ((R : ℝ) + (129 / 200) * L) * (N - R) +
      ((L : ℝ) + (N - R)) * Harmonic N + 3 * N + (L - c : ℕ) := by
  have hcorner := actual_prepared_corner_reduction x p hG hcL hLR hP hLP hroot houtside
    (fun S hS => ⟨(hW S hS).1, (hW S hS).2.1, (hW S hS).2.2.1⟩)
  have hright := actual_prepared_right_joint x p hG hcL hLR hRN hroot houtside
    (fun S hS => ⟨(hW S hS).1, (hW S hS).2.2.2⟩)
  have hEB := actual_EB_count (by omega : c < R) houtside
  have hEX := actual_prepared_EX_width hG hcL hRN hP hLP houtside
  have hcombined : (PreparedCrooked G c L).card + (PreparedAP G c L).card ≤
      (CM (PreparedCrooked G c L) p R).card + (EM (PreparedAP G c L) c R).card +
      (EX (PreparedAP G c L) R).card + R * (N - R) + 2 * N + (L - c) := by
    have hpoly : c * (N - R) + (R - L) * (N - R) +
        (L - c) * (N - R) = R * (N - R) := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    omega
  have hreal : ((PreparedCrooked G c L).card : ℝ) + (PreparedAP G c L).card ≤
      (CM (PreparedCrooked G c L) p R).card + (EM (PreparedAP G c L) c R).card +
      (EX (PreparedAP G c L) R).card + (R : ℝ) * (N - R) + 2 * N + (L - c : ℕ) := by
    have hh : ((PreparedCrooked G c L).card : ℝ) + (PreparedAP G c L).card ≤
        (CM (PreparedCrooked G c L) p R).card + (EM (PreparedAP G c L) c R).card +
        (EX (PreparedAP G c L) R).card + (R * (N - R) : ℕ) + (2 * N : ℕ) +
        (L - c : ℕ) := by exact_mod_cast hcombined
    simpa only [Nat.cast_mul, Nat.cast_sub hRN, Nat.cast_ofNat] using hh
  nlinarith only [hreal, hEX]

#print axioms actual_same_step_endpoint_width
#print axioms actual_large_step_endpoint_width
#print axioms actual_prepared_EX_width
#print axioms actual_prepared_middle_reduction_width
end
end JSP233.ActualExterior208
