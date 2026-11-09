module

public import Erdos272.Resources.RawRecovery208
public import Erdos272.Counting.EndpointFinite208
public import Erdos272.Resources.NoHighTerminalResource208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The actual preparation filters are paid by the local NoHigh theorem
and the kernel-checked endpoint library.  The same family, root and physical
endpoints are retained through the exterior reduction. -/
namespace JSP233.LocalRecovery208
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open PrivatePairExistence ActualPreparation208 ActualExterior208
open EndpointFinite208 NoHighTerminalResource208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def PreparationCost (N L : ℕ) : ℝ :=
  (N : ℝ) * Harmonic N + (27 / 25 : ℝ) * N +
    (L : ℝ) * (2 * Harmonic L + 77 / 25) + 22

def GeometryCost (N L : ℕ) (w : ℝ) : ℝ :=
  (N : ℝ) * Harmonic N + (102 / 25 : ℝ) * N +
    (L : ℝ) * (2 * Harmonic L + 102 / 25) + w * Harmonic N + 22

def LegacyMiddleCost (N : ℕ) : ℝ :=
  (4 * Harmonic N + 2) * N * Harmonic N

theorem actual_preparation_local {N c L : ℕ}
    {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hG : Legal (Ground N) G)
    (hcL : c < L) (hLN : L ≤ N)
    (hroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ G) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z) :
    (G.card : ℝ) ≤ (PreparedCrooked G c L).card +
      (PreparedAP G c L).card + PreparationCost N L := by
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hc1 : 1 ≤ c := by omega
  have hL : 2 ≤ L := by omega
  have hcLow : (c : ℤ) ∈ Ground (L - 1) := by
    apply (mem_ground (L - 1) (c : ℤ)).mpr
    omega
  have hprep := actual_preparation_count_short hN hG hroot (L := (L : ℤ))
  have hprepR : (G.card : ℝ) ≤
      (PreparedCrooked G c L).card + (PreparedAP G c L).card + 3 * N +
      (CrookedMembers G \ HighMembers G c L).card + (LowCut G c).card +
      (HighCut G c L).card := by exact_mod_cast hprep
  have hNo : ((CrookedMembers G \ HighMembers G c L).card : ℝ) ≤
      (L : ℝ) * (Harmonic L + 5) := by
    simpa only [NoHigh208.Failure] using
      actual_failure_five_local hG hroot hP hcP hLP hcLow
  have hLow := actual_low_cut48_25 hG (by omega : 2 ≤ N) hhigh hc1
    (show c ≤ N by omega)
  have hHigh := actual_high_cut48_25 (c := c) hG hL (hLN.trans hhigh)
  dsimp only [PreparationCost]
  nlinarith only [hprepR, hNo, hLow, hHigh]

theorem actual_prepared_losses_width {N c L R : ℕ}
    {G : Finset (Finset ℤ)} {P : Finset ℤ} (x p : Finset ℤ → ℤ)
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hG : Legal (Ground N) G)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ G) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (houtside : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    (hW : ∀ S ∈ PreparedCrooked G c L,
      IntrinsicPair c S {x S, p S} ∧ x S ≤ (R : ℤ) ∧ x S ≠ (L : ℤ) ∧
      ((c : ℤ) < x S → x S < (L : ℤ) → (R : ℤ) < p S →
        S ∩ Finset.Icc (x S) (p S) = {x S, p S} ∨
          ¬ IsAP (S ∩ Finset.Icc (x S) (p S)))) :
    (G.card : ℝ) ≤
      (CM (PreparedCrooked G c L) p R).card + (EM (PreparedAP G c L) c R).card +
      ((R : ℝ) + (129 / 200) * L) * (N - R) +
      GeometryCost N L ((L : ℝ) + (N - R)) := by
  have hprep := actual_preparation_local hN hhigh hc hG hcL (hLR.trans hRN)
    hroot hP hcP hLP
  have hm := actual_prepared_middle_reduction_width x p hG hcL hLR hRN hP hLP
    hroot houtside hW
  have hLC : ((L - c : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.sub_le L c)
  dsimp only [PreparationCost] at hprep
  dsimp only [GeometryCost]
  nlinarith only [hprep, hm, hLC]

theorem actual_readded_local_counts {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    ∃ x p : Finset ℤ → ℤ,
      (∀ S ∈ PreparedCrooked (RawEndpoint114.Readded N F c) c L,
        IntrinsicPair c S {x S, p S} ∧ x S < p S ∧ (L : ℤ) < p S) ∧
      (F.card : ℝ) ≤
        (CM (PreparedCrooked (RawEndpoint114.Readded N F c) c L) p R).card +
        (EM (PreparedAP (RawEndpoint114.Readded N F c) c L) c R).card +
        ((R : ℝ) + (129 / 200) * L) * (N - R) +
        GeometryCost N L ((L : ℝ) + (N - R)) +
        (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  let G := RawEndpoint114.Readded N F (c : ℤ)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS),
     fun S hS U hU hSU => hF.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := RawEndpoint114.actual_retained_subset_readded N F (c : ℤ)
  have hGroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S :=
    RawEndpoint114.actual_readded_root hroot
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c : ℤ)
  have hout : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v := by
    intro S hS hcS
    have hv : S ∈ Avoiders G (c : ℤ) := Finset.mem_filter.mpr ⟨hS, hcS⟩
    change Avoiders G (c : ℤ) = _ at ha
    rw [ha] at hv
    exact houtside S (Finset.mem_filter.mp hv).1 hcS
  obtain ⟨x, p, hx⟩ := actual_prepared_witness_choices hG hGroot
    (by exact_mod_cast hcL.le : (c : ℤ) ≤ L)
    (by exact_mod_cast hLR : (L : ℤ) ≤ R) (hsub hT) hcT hTR
  have hlocal := actual_prepared_losses_width x p hN hhigh hc hG hcL hLR hRN
    hGroot (hsub hP) hcP hLP hout
    (fun S hS => ⟨(hx S hS).1, (hx S hS).2.2.1, (hx S hS).2.2.2.2.1,
      (hx S hS).2.2.2.2.2⟩)
  have hcardR : (G.card : ℝ) + E.card = F.card := by
    exact_mod_cast RawRecovery208.actual_readded_card_identity N F (c : ℤ)
  refine ⟨x, p, (fun S hS => ⟨(hx S hS).1, (hx S hS).2.1,
    (hx S hS).2.2.2.1⟩), ?_⟩
  change (F.card : ℝ) ≤ _ + GeometryCost N L ((L : ℝ) + (N - R)) + E.card
  linarith only [hlocal, hcardR]

theorem actual_readded_raw_profile_local_cuts {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    (F.card : ℝ) ≤ (N : ℝ)^2 / 2 -
      Recovery208.WidthProfile L ((L : ℝ) + (N - R)) + LegacyMiddleCost N +
      GeometryCost N L ((L : ℝ) + (N - R)) +
      (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  obtain ⟨x, p, hW, hcounts⟩ := actual_readded_local_counts hN hhigh hc hF hcL hLR hRN
    hroot hP hcP hLP hT hcT hTR houtside
  let G := RawEndpoint114.Readded N F (c : ℤ)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS),
     fun S hS U hU hSU => hF.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := RawEndpoint114.actual_retained_subset_readded N F (c : ℤ)
  have hm := RawEndpoint115.actual_prepared_CM_EM_profile x p (by omega : 1 ≤ N)
    hG hcL.le hLR hRN (RawEndpoint114.actual_readded_root hroot) (hsub hP) hLP hW
  rw [RawRecovery208.width_profile_eq]
  dsimp only [LegacyMiddleCost]
  nlinarith only [hcounts, hm]

theorem actual_original_raw_profile_local_cuts {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    Recovery208.WidthProfile L ((L : ℝ) + (N - R)) ≤
      LegacyMiddleCost N + GeometryCost N L ((L : ℝ) + (N - R)) + (N : ℝ) / 4 +
      (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  have hr := actual_readded_raw_profile_local_cuts hN hhigh hc hF hcL hLR hRN
    hroot hP hcP hLP hT hcT hTR houtside
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1 ≤ N) hcard
  linarith only [hr, hb]

/-- The true initial deletion fee is inserted once. Restored profiles use
the preceding theorem with their new bound for this same omitted family. -/
theorem actual_original_initial_profile_local_cuts {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 10902 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    Recovery208.WidthProfile L ((L : ℝ) + (N - R)) ≤
      LegacyMiddleCost N + GeometryCost N L ((L : ℝ) + (N - R)) +
      (485 / 4 : ℝ) * N + 968 := by
  have hr := actual_original_raw_profile_local_cuts (by omega : 19 ≤ N) hhigh hc hF
    hcard hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have he := DenseDeletion208.actual_omitted11_affine (c : ℤ) hN hF
  have heR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ) ≤
      121 * (N : ℝ) + 968 := by exact_mod_cast he
  linarith only [hr, heR]

#print axioms actual_preparation_local
#print axioms actual_prepared_losses_width
#print axioms actual_readded_local_counts
#print axioms actual_readded_raw_profile_local_cuts
#print axioms actual_original_raw_profile_local_cuts
#print axioms actual_original_initial_profile_local_cuts
end
end JSP233.LocalRecovery208
