module

public import Erdos272.Counting.APTail208
public import Erdos272.Counting.UnitCount218
public import Erdos272.Geometry.N94488.StepTwoGeometry94488

@[expose] public section

namespace JSP233.APTailThree94488
open StarCompletion APGeometry APCount41 HarmonicAbel29 APTail208
open UnitCount218 StepTwoGeometry94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem reciprocal_square_tail_three {N : ℕ} (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / (d : ℝ)^2) ≤ 79/200 := by
  have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hb := EndpointExterior55.reciprocal_square_tail_two N
  rw [hsplit, Finset.sum_insert (by simp)] at hb
  norm_num at hb ⊢
  linarith only [hb]

theorem harmonic_tail_three {N : ℕ} (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / d) = Harmonic N - 3/2 := by
  have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hb := APTail208.harmonic_tail_two (by omega : 1 ≤ N)
  rw [hsplit, Finset.sum_insert (by simp)] at hb
  norm_num at hb ⊢
  linarith only [hb]

theorem actual_large_step_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (htwo : ∀ S ∈ F, 2 ≤ S.card)
    (hlarge : ∀ S ∈ F, 3 ≤ Step S) :
    (F.card : ℝ) ≤ (79 / 800 : ℝ) * N^2 + (N : ℝ) * (Harmonic N - 3/2) := by
  have hmaps : ∀ S ∈ F, Step S ∈ Finset.Icc 3 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨hlarge S hS,
      actual_step_bound (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card : ℝ) =
      ∑ d ∈ Finset.Icc 3 N, ((F.filter (fun S => Step S = d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ d ∈ Finset.Icc 3 N,
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
      (N : ℝ)^2 / 4 * (∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / (d : ℝ)^2) +
      (N : ℝ) * (Harmonic N - 3/2) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 3 N,
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
          harmonic_tail_three hN]
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail_three hN)
    (show (0 : ℝ) ≤ (N : ℝ)^2 / 4 by positivity)
  nlinarith only [hsum, hquad]

theorem actual_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ) ≤ (UnitAP F).card+(StepTwo F).card+
      (79/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*(Harmonic N-3/2)+1 := by
  let P := F.filter IsAP
  let A := P.filter fun S => 2 ≤ S.card
  let C := P.filter fun S => ¬2 ≤ S.card
  let U := A.filter fun S => Step S = 1
  let R := A.filter fun S => ¬Step S = 1
  let B := R.filter fun S => Step S = 2
  let D := R.filter fun S => ¬Step S = 2
  have hPF : P ⊆ F := Finset.filter_subset _ _
  have hAP : A ⊆ P := Finset.filter_subset _ _
  have hAF : A ⊆ F := hAP.trans hPF
  have hCF : C ⊆ F := (Finset.filter_subset _ _).trans hPF
  have hRA : R ⊆ A := Finset.filter_subset _ _
  have hDR : D ⊆ R := Finset.filter_subset _ _
  have hDF : D ⊆ F := hDR.trans (hRA.trans hAF)
  have hsub : ∀ G : Finset (Finset ℤ), G ⊆ F → Legal (Ground N) G := by
    intro G hGF
    exact ⟨fun S hS => hF.1 S (hGF hS),
      fun S hS T hT hn => hF.2 S (hGF hS) T (hGF hT) hn⟩
  have hDP : ∀ S ∈ D, IsAP S := fun S hS =>
    (Finset.mem_filter.mp (hAP (hRA (hDR hS)))).2
  have ht := actual_large_step_count hN (hsub D hDF) hDP
    (fun S hS => (Finset.mem_filter.mp (hRA (hDR hS))).2)
    (fun S hS => by
      have hp := (actual_step (hDP S hS)).1
      have h1 := (Finset.mem_filter.mp (hDR hS)).2
      have h2 := (Finset.mem_filter.mp hS).2
      omega)
  have hs := actual_singleton_family_count (hsub C hCF)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hU : U = UnitAP F := by
    ext S
    simp only [U, A, P, UnitAP, Finset.mem_filter]
    tauto
  have hB : B = StepTwo F := by
    ext S
    simp only [B, R, A, P, StepTwo, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨⟨hSF, hSA⟩, htwo⟩, h1⟩, h2⟩
      exact ⟨hSF, hSA, htwo, h2⟩
    · rintro ⟨hSF, hSA, htwo, h2⟩
      exact ⟨⟨⟨⟨hSF, hSA⟩, htwo⟩, by omega⟩, h2⟩
  have hp := Finset.card_filter_add_card_filter_not (s := P) (fun S => 2 ≤ S.card)
  have hq := Finset.card_filter_add_card_filter_not (s := A) (fun S => Step S = 1)
  have hr := Finset.card_filter_add_card_filter_not (s := R) (fun S => Step S = 2)
  change A.card+C.card = P.card at hp
  change U.card+R.card = A.card at hq
  change B.card+D.card = R.card at hr
  have hpR : (A.card : ℝ)+C.card = P.card := by exact_mod_cast hp
  have hqR : (U.card : ℝ)+R.card = A.card := by exact_mod_cast hq
  have hrR : (B.card : ℝ)+D.card = R.card := by exact_mod_cast hr
  have hsR : (C.card : ℝ) ≤ 1 := by exact_mod_cast hs
  rw [hU] at hqR
  rw [hB] at hrR
  change (P.card : ℝ) ≤ _
  nlinarith only [ht, hpR, hqR, hrR, hsR]

#print axioms reciprocal_square_tail_three
#print axioms harmonic_tail_three
#print axioms actual_large_step_count
#print axioms actual_AP_count
end
end JSP233.APTailThree94488
