module

public import Erdos272.Resources.MaximumCore208

@[expose] public section

namespace JSP233.CoreCoordinates208
open StarCompletion APGeometry SourceBridge208 NearAP36 MaximumCore208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem defect_positive {N : ℕ} {S : Finset ℤ} (hS : 2 ≤ S.card)
    (hground : S ⊆ Ground N) (hbad : ¬IsAP S) : 1 ≤ Defect S := by
  obtain ⟨a,d,hd,hsub,hrem⟩ := actual_maximum_core hS hground
  have htwo := two_le_maxAPSize hS
  by_contra hn
  have hz : (S \ Grid a d (MaxAPSize S)).card=0 := by omega
  have he : S \ Grid a d (MaxAPSize S) = ∅ := Finset.card_eq_zero.mp hz
  have hreverse : S ⊆ Grid a d (MaxAPSize S) := Finset.sdiff_eq_empty_iff_subset.mp he
  have hEq := Finset.Subset.antisymm hsub hreverse
  exact hbad (hEq ▸ grid_isAP a d (MaxAPSize S) hd (by omega))

theorem actual_coordinate_selection {N T E U : ℕ} {F : Finset (Finset ℤ)}
    (hT : 2 ≤ T) (hET : E ≤ T) (hground : ∀ S ∈ F, S ⊆ Ground N)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E) :
    ∃ start step : Finset ℤ → ℕ, ∀ S ∈ F,
      0 < step S ∧ Grid (start S) (step S) (MaxAPSize S) ⊆ S ∧
      T-E+1 ≤ MaxAPSize S ∧ MaxAPSize S ≤ U-2 ∧
      (S \ Grid (start S) (step S) (MaxAPSize S)).card = Defect S := by
  have hex : ∀ S : Finset ℤ, ∃ a d : ℕ, S ∈ F →
      0 < d ∧ Grid a d (MaxAPSize S) ⊆ S ∧
      T-E+1 ≤ MaxAPSize S ∧ MaxAPSize S ≤ U-2 ∧
      (S \ Grid a d (MaxAPSize S)).card = Defect S := by
    intro S
    by_cases hSF : S ∈ F
    · have hs := hlow S hSF
      have hS : 2 ≤ S.card := by omega
      obtain ⟨a,d,hd,hsub,hrem⟩ := actual_maximum_core hS (hground S hSF)
      have hp := defect_positive hS (hground S hSF) (hbad S hSF)
      have hmax := maxAPSize_le_card S
      have hfee := hsmall S hSF
      have hh := hhigh S hSF
      unfold Defect at hp hfee
      refine ⟨a,d,fun _ => ⟨hd,hsub,by omega,by omega,hrem⟩⟩
    · exact ⟨0,1,fun hs => False.elim (hSF hs)⟩
  choose a d hcoords using hex
  exact ⟨a,d,hcoords⟩

#print axioms defect_positive
#print axioms actual_coordinate_selection
end
end JSP233.CoreCoordinates208
