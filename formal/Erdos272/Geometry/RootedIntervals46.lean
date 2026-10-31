import Erdos272.Counting.WitnessInterval43

/-! Actual rooted interval members outside the strict straddled class consume
only the two physical endpoint images of Ground N. -/
namespace JSP233.RootedIntervals46
open StarCompletion WitnessInterval43
open scoped Classical
noncomputable section

def RootedIntervals (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S=>c∈S ∧ ∃ a b:ℤ,S=Finset.Icc a b)

def BoundaryPool (N : ℕ) (c : ℤ) : Finset (Finset ℤ) :=
  (Ground N).image (fun a=>Finset.Icc a c)∪(Ground N).image (fun b=>Finset.Icc c b)

theorem straddled_subset_rooted (F : Finset (Finset ℤ)) (c : ℤ) :
    StraddledIntervals F c⊆RootedIntervals F c := by
  intro S hS
  obtain ⟨hSF,a,b,hac,hcb,rfl⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_filter.mpr ⟨hSF,Finset.mem_Icc.mpr ⟨hac.le,hcb.le⟩,a,b,rfl⟩

theorem actual_boundary_endpoints {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {S : Finset ℤ}
    (hground : ∀ T∈F,T⊆Ground N)
    (hS : S∈RootedIntervals F c\StraddledIntervals F c) :
    (∃ a∈Ground N,S=Finset.Icc a c) ∨ (∃ b∈Ground N,S=Finset.Icc c b) := by
  obtain ⟨hroot,hnot⟩ := Finset.mem_sdiff.mp hS
  obtain ⟨hSF,hcS,a,b,hrep⟩ := Finset.mem_filter.mp hroot
  subst S
  have hcb := Finset.mem_Icc.mp hcS
  have hab : a≤b := by omega
  have haG := hground _ hSF (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
  have hbG := hground _ hSF (Finset.mem_Icc.mpr ⟨hab,le_rfl⟩)
  by_cases hac : a=c
  · exact Or.inr ⟨b,hbG,by rw [hac]⟩
  · have hbc : b=c := by
      by_contra hbc
      apply hnot
      exact Finset.mem_filter.mpr ⟨hSF,a,b,by omega,by omega,rfl⟩
    exact Or.inl ⟨a,haG,by rw [hbc]⟩

theorem actual_boundary_cover (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hground : ∀ T∈F,T⊆Ground N) :
    RootedIntervals F c\StraddledIntervals F c⊆BoundaryPool N c := by
  intro S hS
  rcases actual_boundary_endpoints hground hS with ⟨a,ha,rfl⟩|⟨b,hb,rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)

theorem actual_boundary_card_le (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hground : ∀ T∈F,T⊆Ground N) :
    (RootedIntervals F c\StraddledIntervals F c).card≤2*N := by
  have hc := Finset.card_le_card (actual_boundary_cover N F c hground)
  have hL : ((Ground N).image (fun a=>Finset.Icc a c)).card≤N :=
    Finset.card_image_le.trans_eq (ground_card N)
  have hR : ((Ground N).image (fun b=>Finset.Icc c b)).card≤N :=
    Finset.card_image_le.trans_eq (ground_card N)
  have hu := Finset.card_union_le ((Ground N).image (fun a=>Finset.Icc a c))
    ((Ground N).image (fun b=>Finset.Icc c b))
  dsimp only [BoundaryPool] at hc
  omega

theorem actual_rooted_intervals_card_le (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hground : ∀ T∈F,T⊆Ground N) :
    (RootedIntervals F c).card≤(StraddledIntervals F c).card+2*N := by
  have hp := Finset.card_sdiff_add_card_eq_card (straddled_subset_rooted F c)
  have hb := actual_boundary_card_le N F c hground
  omega

theorem actual_legal_rooted_intervals_card_le (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hF : Legal (Ground N) F) :
    (RootedIntervals F c).card≤(StraddledIntervals F c).card+2*N :=
  actual_rooted_intervals_card_le N F c hF.1

#print axioms straddled_subset_rooted
#print axioms actual_boundary_endpoints
#print axioms actual_boundary_cover
#print axioms actual_boundary_card_le
#print axioms actual_rooted_intervals_card_le
#print axioms actual_legal_rooted_intervals_card_le
end
end JSP233.RootedIntervals46
