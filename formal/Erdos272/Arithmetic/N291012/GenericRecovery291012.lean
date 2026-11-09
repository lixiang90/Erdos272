module

public import Erdos272.Resources.CovarianceFamily214

@[expose] public section

namespace JSP233.GenericRecovery291012
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open PrivatePairExistence ActualPreparation208 ActualExterior208 LocalRecovery208
open CovarianceFamily214
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Readded (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F \ TerminalDeficit51.OmittedAvoiders N r F c

theorem actual_retained_subset_readded (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Retained N r F ⊆ Readded N r F c := by
  intro S hS
  obtain ⟨hSF, hnot⟩ := Finset.mem_sdiff.mp hS
  apply Finset.mem_sdiff.mpr
  refine ⟨hSF, ?_⟩
  intro hE
  exact hnot (Finset.mem_filter.mp hE).1

/-- The readded root-bearing deleted members cause no new avoider. -/
theorem actual_readded_root {N r : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S ∈ Retained N r F, ¬ IsAP S → c ∈ S) :
    ∀ S ∈ Readded N r F c, ¬ IsAP S → c ∈ S := by
  intro S hS hbad
  by_contra hcS
  have hv : S ∈ Avoiders (Readded N r F c) c := Finset.mem_filter.mpr ⟨hS, hcS⟩
  have ha := TerminalDeficit51.actual_avoider_readdition N r F c
  change Avoiders (Readded N r F c) c = _ at ha
  rw [ha] at hv
  exact hcS (hroot S (Finset.mem_filter.mp hv).1 hbad)

/-- The old complete prepared-family raw estimate now pays all of the
readded family.  Only actual deleted avoiders, not all deleted members, remain.
No cardinality estimate for those avoiders is assumed here. -/

theorem actual_card_identity (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    (Readded N r F c).card + (TerminalDeficit51.OmittedAvoiders N r F c).card = F.card := by
  apply Finset.card_sdiff_add_card_eq_card
  exact (Finset.filter_subset _ _).trans (actual_deleted_subset N r F)

theorem actual_readded_local_counts {N c L R r : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 853476)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N r F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N r F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N r F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N r F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    ∃ x p : Finset ℤ → ℤ,
      (∀ S ∈ PreparedCrooked (Readded N r F c) c L,
        IntrinsicPair c S {x S, p S} ∧ x S < p S ∧ (L : ℤ) < p S) ∧
      (F.card : ℝ) ≤
        (CM (PreparedCrooked (Readded N r F c) c L) p R).card +
        (EM (PreparedAP (Readded N r F c) c L) c R).card +
        ((R : ℝ) + (129 / 200) * L) * (N - R) +
        GeometryCost N L ((L : ℝ) + (N - R)) +
        (TerminalDeficit51.OmittedAvoiders N r F (c : ℤ)).card := by
  let E := TerminalDeficit51.OmittedAvoiders N r F (c : ℤ)
  let G := Readded N r F (c : ℤ)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS),
     fun S hS U hU hSU => hF.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := actual_retained_subset_readded N r F (c : ℤ)
  have hGroot : ∀ S ∈ G, ¬ IsAP S → (c : ℤ) ∈ S :=
    actual_readded_root hroot
  have ha := TerminalDeficit51.actual_avoider_readdition N r F (c : ℤ)
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
    exact_mod_cast actual_card_identity N r F (c : ℤ)
  refine ⟨x, p, (fun S hS => ⟨(hx S hS).1, (hx S hS).2.1,
    (hx S hS).2.2.2.1⟩), ?_⟩
  change (F.card : ℝ) ≤ _ + GeometryCost N L ((L : ℝ) + (N - R)) + E.card
  linarith only [hlocal, hcardR]

theorem actual_readded_raw_profile_local {N c L R r : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 720896)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N r F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N r F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N r F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N r F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    :
    (F.card : ℝ) ≤ (N : ℝ)^2/2-
      Recovery208.WidthProfile L ((L : ℝ)+(N-R)) + MiddleCost L+
      GeometryCost N L ((L : ℝ)+(N-R))+
      (TerminalDeficit51.OmittedAvoiders N r F (c : ℤ)).card := by
  obtain ⟨x,p,hW,hcounts⟩ := actual_readded_local_counts hN (by omega : N≤853476) hc hF hcL hLR hRN
    hroot hP hcP hLP hT hcT hTR houtside
  let G := Readded N r F (c : ℤ)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS), fun S hS U hU hSU => hF.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := actual_retained_subset_readded N r F (c : ℤ)
  have hm := actual_prepared_middle_local x p (by omega : 1≤L) (by omega : N≤720896)
    hcL.le hLR hRN hG (actual_readded_root hroot) (hsub hP) hLP hW
  rw [RawRecovery208.width_profile_eq]
  linarith only [hcounts,hm]

theorem actual_original_raw_profile_local {N c L R r : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 720896)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀ S ∈ Retained N r F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N r F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N r F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N r F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    :
    Recovery208.WidthProfile L ((L : ℝ)+(N-R)) ≤
      MiddleCost L+GeometryCost N L ((L : ℝ)+(N-R))+(N : ℝ)/4+
      (TerminalDeficit51.OmittedAvoiders N r F (c : ℤ)).card := by
  have hr := actual_readded_raw_profile_local hN hhigh hc hF hcL hLR hRN hroot hP hcP hLP
    hT hcT hTR houtside
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  linarith only [hr,hb]

#print axioms actual_retained_subset_readded
#print axioms actual_readded_root
#print axioms actual_card_identity
#print axioms actual_readded_local_counts
#print axioms actual_readded_raw_profile_local
#print axioms actual_original_raw_profile_local
end
end JSP233.GenericRecovery291012
