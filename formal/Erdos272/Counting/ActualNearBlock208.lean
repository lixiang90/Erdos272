module

public import Erdos272.Resources.CoreCoordinates208
public import Erdos272.Counting.PotentialPhases208
public import Erdos272.Arithmetic.StepClass208

@[expose] public section

namespace JSP233.ActualNearBlock208
open StarCompletion APGeometry SourceBridge208 NearAP36 StepClass208 ShiftedBlocks208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_same_code_count {N d T E B : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hB : 0 < B) (hBA : B ≤ T-E) (hET : E ≤ T)
    (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S)
    (hsmall : ∀ S ∈ F, Defect S < E)
    (hcode : ∀ S ∈ F, ∀ R ∈ F, Code d B (start S) = Code d B (start R))
    (hgate : (PrimeGate d-1)*(T-E+1-B) ≥ E ∨
      PrimeGate d*B ≤ (PrimeGate d-1)*(T-E+1)) : F.card ≤ N := by
  let core : Finset ℤ → Finset ℤ := fun S => Grid (start S) d (MaxAPSize S)
  have hp : 2 ≤ PrimeGate d := by unfold PrimeGate; split_ifs <;> norm_num
  have hmaxlow : ∀ S ∈ F, T-E+1 ≤ MaxAPSize S := by
    intro S hS
    have hs := hlow S hS
    have he := hsmall S hS
    have hm := maxAPSize_le_card S
    unfold Defect at he
    omega
  have hrem : ∀ S ∈ F, (S \ core S).card = Defect S := by
    intro S hS
    have hh := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    rw [grid_card _ _ _ hd] at hh
    unfold Defect
    dsimp [core]
    omega
  have hAP : ∀ S ∈ F, IsAP (core S) := by
    intro S hS
    exact grid_isAP _ _ _ hd (by have hh := hmaxlow S hS; omega)
  apply crooked_disjoint_remainders_card hF.1 core hbad hAP hsub
  intro S hS R hR hne
  have hsmallS : (S \ core S).card < E := by rw [hrem S hS]; exact hsmall S hS
  have hsmallR : (R \ core R).card < E := by rw [hrem R hR]; exact hsmall R hR
  exact ShiftedBlocks208.actual_pair_remainders_disjoint hF hS hR hne hd hB hBA hp
    (hmaxlow S hS) (hmaxlow R hR) (hcode S hS R hR) (hsub S hS) (hsub R hR)
    hsmallS hsmallR hgate (fun delta hdelta hdiv hlt => actual_ratio d hdelta hdiv hlt)
    (fun P hP hPS => AP_card_le_max hP hPS) (fun P hP hPR => AP_card_le_max hP hPR)

#print axioms actual_same_code_count
end
end JSP233.ActualNearBlock208
