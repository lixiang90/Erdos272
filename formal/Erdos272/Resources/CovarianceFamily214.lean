import Erdos272.Resources.CovarianceWindow213
import Erdos272.Resources.LocalResourceRecovery208
namespace JSP233.CovarianceFamily214
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open PrivatePairExistence ActualPreparation208 ActualExterior208 LocalRecovery208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def MiddleCost (L : ℕ) : ℝ := (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850

theorem actual_prepared_middle_local {N c L R : ℕ} {G : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p : Finset ℤ → ℤ)
    (hL : 1≤L) (hhigh : N≤720896) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hG : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c : ℤ)∈S)
    (hP : P∈G) (hLP : ∀z∈P,(L : ℤ)≤z)
    (hW : ∀S∈PreparedCrooked G c L,
      IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L : ℤ)<p S) :
    ((CM (PreparedCrooked G c L) p R).card : ℝ)+(EM (PreparedAP G c L) c R).card+
      ((R : ℝ)+(129/200)*L)*(N-R) ≤
      (N : ℝ)^2/2-RawEndpoint115.ProfileDeficit L (N-R)+MiddleCost L := by
  obtain ⟨e,he,hcount⟩ := MiddleJoint51.actual_prepared_middle_resource_sum x p hG hcL hLR hRN
    hroot hP hLP hW
  have hm := CovarianceWindow213.actual_middle_profile hL hcL hLR hRN hhigh e he
  have hc : ((CM (PreparedCrooked G c L) p R).card : ℝ)+(EM (PreparedAP G c L) c R).card ≤
      ((∑d∈Finset.Icc 1 N,
        MiddleJoint51.ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  dsimp only [MiddleCost]
  linarith only [hm,hc]

theorem actual_readded_raw_profile_local {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 720896)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    :
    (F.card : ℝ) ≤ (N : ℝ)^2/2-
      Recovery208.WidthProfile L ((L : ℝ)+(N-R)) + MiddleCost L+
      GeometryCost N L ((L : ℝ)+(N-R))+
      (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  obtain ⟨x,p,hW,hcounts⟩ := actual_readded_local_counts hN (by omega : N≤853476) hc hF hcL hLR hRN
    hroot hP hcP hLP hT hcT hTR houtside
  let G := RawEndpoint114.Readded N F (c : ℤ)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS), fun S hS U hU hSU => hF.2 S (hGF hS) U (hGF hU) hSU⟩
  have hsub := RawEndpoint114.actual_retained_subset_readded N F (c : ℤ)
  have hm := actual_prepared_middle_local x p (by omega : 1≤L) (by omega : N≤720896)
    hcL.le hLR hRN hG (RawEndpoint114.actual_readded_root hroot) (hsub hP) hLP hW
  rw [RawRecovery208.width_profile_eq]
  linarith only [hcounts,hm]

theorem actual_original_raw_profile_local {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 19 ≤ N) (hhigh : N ≤ 720896)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    :
    Recovery208.WidthProfile L ((L : ℝ)+(N-R)) ≤
      MiddleCost L+GeometryCost N L ((L : ℝ)+(N-R))+(N : ℝ)/4+
      (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  have hr := actual_readded_raw_profile_local hN hhigh hc hF hcL hLR hRN hroot hP hcP hLP
    hT hcT hTR houtside
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  linarith only [hr,hb]

theorem actual_original_initial_profile_local {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 10902≤N) (hhigh : N≤720896)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    :
    Recovery208.WidthProfile L ((L : ℝ)+(N-R)) ≤
      ((Harmonic N+6279/50)*(N : ℝ))+
      (102/25+2*Harmonic L+CovarianceScalar213.Polynomial (Real.log L))*(L : ℝ)+
      Harmonic N*((L : ℝ)+(N-R))+1840 := by
  have hr := actual_original_raw_profile_local (by omega : 19≤N) hhigh hc hF hcard
    hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have he := DenseDeletion208.actual_omitted11_affine (c : ℤ) hN hF
  have heR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ) ≤
      121*(N : ℝ)+968 := by exact_mod_cast he
  dsimp only [MiddleCost,GeometryCost] at hr
  nlinarith only [hr,heR,(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

#print axioms actual_prepared_middle_local
#print axioms actual_readded_raw_profile_local
#print axioms actual_original_raw_profile_local
#print axioms actual_original_initial_profile_local
end
end JSP233.CovarianceFamily214
