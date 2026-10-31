import Erdos272.Resources.RawEndpoint115
import Erdos272.Resources.ActualExterior208
import Erdos272.Resources.Recovery208
import Erdos272.Resources.DenseDeletion208
import Erdos272.Resources.ActualPreparation208

/-! The actual readded family is retained in this bridge.  Its omitted
avoider count is paid exactly once, with no independent family chosen. -/
namespace JSP233.RawRecovery208
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 HarmonicLog55
open APCount41 APExterior50 APPrepare49 PreparedClasses50 PreparedWitness48
open RestrictedWitness44 MiddleCoordinates51
open ActualPreparation208 ActualExterior208
open PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem width_profile_eq (L x : ℝ) :
    Recovery208.WidthProfile L (L + x) = RawEndpoint115.ProfileDeficit L x := by
  dsimp only [Recovery208.WidthProfile, RawEndpoint115.ProfileDeficit]
  ring

theorem actual_readded_card_identity (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    (RawEndpoint114.Readded N F c).card +
      (TerminalDeficit51.OmittedAvoiders N 11 F c).card = F.card := by
  have hEF : TerminalDeficit51.OmittedAvoiders N 11 F c ⊆ F :=
    (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  exact Finset.card_sdiff_add_card_eq_card hEF

theorem actual_original_raw_width_profile {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T) (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    Recovery208.WidthProfile L ((L : ℝ) + ((N : ℝ) - R)) ≤
      N * SimplexPolynomial (Real.log N) (Harmonic N) / 2 +
      4 * N * (Harmonic N)^2 + 6 * N * Harmonic N + (97 / 4 : ℝ) * N +
      (L - c : ℕ) + 3 + (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hN : 1 ≤ N := by omega
  have hr := RawEndpoint115.actual_readded11_raw_profile hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hb := RawEndpoint113.original_quarter_card_lower hN hcard
  rw [width_profile_eq]
  nlinarith only [hr, hb]

/-- The initial all-pairs deletion price is substituted into the original
family estimate once. Later restoration estimates should use the preceding
theorem with their new omitted-avoider count instead of adding this price. -/
theorem actual_original_initial_raw_width_profile {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 10902 ≤ N) (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T) (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    Recovery208.WidthProfile L ((L : ℝ) + ((N : ℝ) - R)) ≤
      N * SimplexPolynomial (Real.log N) (Harmonic N) / 2 +
      4 * N * (Harmonic N)^2 + 6 * N * Harmonic N + (581 / 4 : ℝ) * N +
      (L - c : ℕ) + 971 := by
  have hr := actual_original_raw_width_profile hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have he := DenseDeletion208.actual_omitted11_affine (c : ℤ) hN hF
  have heR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ) ≤
      121 * (N : ℝ) + 968 := by exact_mod_cast he
  linarith only [hr, heR]

theorem actual_prepared_family_raw_profile_counts {N c L R : ℕ}
    {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c : ℤ) ∈ Ground N) (hG : Legal (Ground N) G)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ G) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ G) (hcT : (c : ℤ) ∉ T) (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    (G.card : ℝ) ≤ (N : ℝ)^2 / 2 - Recovery208.WidthProfile L ((L : ℝ) + (N - R)) +
      (4 * Harmonic N + 2) * N * Harmonic N +
      ((L : ℝ) + (N - R)) * Harmonic N + 4 * N + (L - c : ℕ) +
      (CrookedMembers G \ HighMembers G c L).card + (LowCut G c).card +
      (HighCut G c L).card + (SmallAP G).card := by
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hN : 1 ≤ N := by omega
  obtain ⟨x, p, hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c : ℤ) ≤ L)
    (by exact_mod_cast hLR : (L : ℤ) ≤ R) hT hcT hTR
  have hprep := actual_preparation_count (L := (L : ℤ)) hG hroot
  have hprepR : (G.card : ℝ) ≤ (PreparedCrooked G c L).card + (PreparedAP G c L).card +
      (N : ℝ) + (CrookedMembers G \ HighMembers G c L).card + (LowCut G c).card +
      (HighCut G c L).card + (SmallAP G).card := by exact_mod_cast hprep
  have hm := actual_prepared_middle_reduction_width x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS => ⟨(hx S hS).1, (hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1, (hx S hS).2.2.2.2.2⟩)
  have hr := RawEndpoint115.actual_prepared_CM_EM_profile x p hN hG hcL.le hLR hRN hroot
    hP hLP (fun S hS => ⟨(hx S hS).1, (hx S hS).2.1, (hx S hS).2.2.2.1⟩)
  rw [width_profile_eq]
  nlinarith only [hprepR, hm, hr]

#print axioms actual_readded_card_identity
#print axioms actual_original_raw_width_profile
#print axioms actual_original_initial_raw_width_profile
#print axioms actual_preparation_count
#print axioms actual_small_AP_cut_count
#print axioms actual_preparation_count_short
#print axioms actual_prepared_family_raw_profile_counts
end
end JSP233.RawRecovery208
