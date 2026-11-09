module

public import Erdos272.Resources.SourceBridge208
public import Erdos272.Resources.CoreBlock208

@[expose] public section

namespace JSP233.MaximumCore208
open StarCompletion APGeometry SourceBridge208 NearAP36 CoreBlock208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_maximum_core {N : ℕ} {S : Finset ℤ} (hS : 2 ≤ S.card)
    (hground : S ⊆ Ground N) : ∃ a d : ℕ, 0 < d ∧
      Grid a d (MaxAPSize S) ⊆ S ∧
      (S \ Grid a d (MaxAPSize S)).card = Defect S := by
  let A := S.powerset.filter IsAP
  have hA : A.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    refine ⟨{x,y}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, pair_isAP x y⟩⟩
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hPS : P ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hAP : IsAP P := (Finset.mem_filter.mp hP).2
  have hcard : P.card = MaxAPSize S := by
    apply Nat.le_antisymm (AP_card_le_max hAP hPS)
    exact Finset.sup_le hmax
  obtain ⟨a,d,hd,hform⟩ := actual_AP_grid_representation (hPS.trans hground) hAP
  refine ⟨a,d,hd,?_,?_⟩
  · rw [←hcard, ←hform]
    exact hPS
  · rw [←hcard, ←hform]
    have hh := Finset.card_sdiff_add_card_eq_card hPS
    unfold Defect
    omega

theorem actual_maximum_block_count {N d A B E p : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hB : 0 < B) (hBA : B ≤ A) (hp : 2 ≤ p)
    (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, A+1 ≤ MaxAPSize S)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S)
    (hsmall : ∀ S ∈ F, Defect S < E)
    (hcode : ∀ S ∈ F, ∀ T ∈ F, StartCode d B (start S) = StartCode d B (start T))
    (hgate : (p - 1) * (A + 1 - B) ≥ E ∨ p * B ≤ (p - 1) * (A + 1))
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ (d : ℤ) → delta < d → (p : ℤ) * delta ≤ d) :
    F.card ≤ N := by
  let core : Finset ℤ → Finset ℤ := fun S => Grid (start S) d (MaxAPSize S)
  have hrem : ∀ S ∈ F, (S \ core S).card = Defect S := by
    intro S hS
    have hh := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    rw [grid_card _ _ _ hd] at hh
    unfold Defect
    dsimp [core]
    omega
  have hAP : ∀ S ∈ F, IsAP (core S) := by
    intro S hS
    apply grid_isAP _ _ _ hd
    have hh := hlow S hS
    omega
  apply crooked_disjoint_remainders_card hF.1 core hbad hAP hsub
  intro S hS T hT hne
  have hsmallS : (S \ core S).card < E := by rw [hrem S hS]; exact hsmall S hS
  have hsmallT : (T \ core T).card < E := by rw [hrem T hT]; exact hsmall T hT
  exact actual_pair_remainders_disjoint hF hS hT hne hd hB hBA hp
    (hlow S hS) (hlow T hT) (hcode S hS T hT) (hsub S hS) (hsub T hT)
    hsmallS hsmallT hgate hproper (fun R hR hRS => AP_card_le_max hR hRS)
    (fun R hR hRT => AP_card_le_max hR hRT)

#print axioms actual_maximum_core
#print axioms actual_maximum_block_count
end
end JSP233.MaximumCore208
