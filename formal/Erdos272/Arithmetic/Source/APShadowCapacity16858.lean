module

public import Erdos272.Resources.IntrinsicTriples208

@[expose] public section

/-! Recompile the actual AP-family shadow argument in the private 16858
closure; its older UnitShadowScalar218 module is outside the sealed root. -/
namespace JSP233.APShadowCapacity16858
open StarCompletion IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def APShadow (U : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  U.biUnion (fun P => P.powersetCard 3)

theorem actual_AP_family_capacity {Ω : Finset ℤ} {F U : Finset (Finset ℤ)}
    (hF : Legal Ω F) (hUF : U ⊆ F) (hAP : ∀ P ∈ U, IsAP P) :
    (∑ S ∈ F, (Pool S).card) + (APShadow U).card ≤ Ω.card.choose 3 := by
  have hd : Disjoint (F.biUnion Pool) (APShadow U) := by
    apply Finset.disjoint_left.mpr
    intro Q hQ hQU
    obtain ⟨P, hPU, hQP⟩ := Finset.mem_biUnion.mp hQU
    exact Finset.disjoint_left.mp
      (disjoint_actual_AP hF (hUF hPU) (hAP P hPU)) hQ hQP
  have hs : APShadow U ⊆ Ω.powersetCard 3 := by
    intro Q hQ
    obtain ⟨P, hPU, hQP⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQP
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans (hF.1 P (hUF hPU)), hcard⟩
  have hsub : F.biUnion Pool ∪ APShadow U ⊆ Ω.powersetCard 3 :=
    Finset.union_subset (union_subset_triples hF.1) hs
  calc
    _ = (F.biUnion Pool).card + (APShadow U).card := by
      rw [Finset.card_biUnion (pools_pairwise_disjoint hF)]
    _ = (F.biUnion Pool ∪ APShadow U).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (Ω.powersetCard 3).card := Finset.card_le_card hsub
    _ = _ := Finset.card_powersetCard 3 Ω

#print axioms actual_AP_family_capacity
end
end JSP233.APShadowCapacity16858
