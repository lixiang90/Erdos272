module

public import Erdos272.Geometry.CrossLine30
public import Erdos272.Resources.StarBudget30

@[expose] public section

/-! The complete common-point upper bound for actual finite integer sets.
No StarBound, line estimate, affine normalization or supply inequality is
assumed by the final theorem. -/
namespace JSP233.StarBound30
open StarCompletion StarResources30 StarBudget30 CrossLine30
open scoped Classical
noncomputable section

theorem physical_rooted_bound (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Finset.Icc (1:ℤ) (N:ℤ))
    (hlegal : Legal (Finset.Icc (1:ℤ) (N:ℤ)) F) (hroot : Rooted F c) :
    F.card≤N.choose 2+1+(N-1)/4 := by
  have hAPmem : ∀ S∈APLarge F, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hrootAP : Rooted (APLarge F) c := fun S hS => hroot S (Finset.mem_filter.mp hS).1
  have hgroundAP : ∀ S∈APLarge F, S⊆Finset.Icc (1:ℤ) (N:ℤ) :=
    fun S hS => hlegal.1 S (Finset.mem_filter.mp hS).1
  have hactive : (APActiveSteps c (APLarge F)).card≤(N-1)/4 := by
    apply active_steps_card_le N c
    intro d hd
    obtain ⟨hdpos,hL,hR⟩ := active_step_geometry c _ (APLarge F) hAPmem hrootAP hgroundAP hd
    exact ⟨hdpos,(Finset.mem_Icc.mp hL).1,(Finset.mem_Icc.mp hR).2⟩
  exact physical_rooted_bound_of_APLarge N F c hc hlegal hroot _ hactive
    (actual_APLarge_count_le_covered c _ F hlegal.1 hroot)

theorem physical_starBound (N : ℕ) :
    StarBound (Finset.Icc (1:ℤ) (N:ℤ)) (N.choose 2+1+(N-1)/4) := by
  intro F hlegal hstar
  obtain ⟨c,hc,hroot⟩ := hstar
  exact physical_rooted_bound N F c hc hlegal hroot

#print axioms physical_rooted_bound
#print axioms physical_starBound
end
end JSP233.StarBound30
