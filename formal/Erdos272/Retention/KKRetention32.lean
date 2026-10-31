import Erdos272.Resources.JointResources31

/-! Actual AP-retaining deletion bookkeeping. This module does not assert an
external KK reduction or an omitter counting bound. -/
namespace JSP233.KKRetention32
open StarCompletion
open scoped Classical
noncomputable section

def APRetained (F G : Finset (Finset ℤ)) : Prop :=
  ∀ S∈F, IsAP S → S∈G

theorem apRetained_refl (F : Finset (Finset ℤ)) : APRetained F F := by
  intro S hS _
  exact hS

theorem apRetained_trans (F G H : Finset (Finset ℤ))
    (hFG : APRetained F G) (hGH : APRetained G H) : APRetained F H := by
  intro S hS hAP
  exact hGH S (hFG S hS hAP) hAP

theorem retained_legal (Ω : Finset ℤ) (F G : Finset (Finset ℤ))
    (hlegal : Legal Ω F) (hGF : G⊆F) : Legal Ω G := by
  constructor
  · intro S hS
    exact hlegal.1 S (hGF hS)
  · intro S hS T hT hne
    exact hlegal.2 S (hGF hS) T (hGF hT) hne

theorem retained_root_mem_ground (Ω : Finset ℤ) (F G : Finset (Finset ℤ))
    (r : ℤ) (hground : ∀ S∈F, S⊆Ω) (hGF : G⊆F)
    (hne : G.Nonempty) (hroot : Rooted G r) : r∈Ω := by
  obtain ⟨S,hSG⟩ := hne
  exact hground S (hGF hSG) (hroot S hSG)

theorem avoiders_subset_difference (F G : Finset (Finset ℤ)) (r : ℤ)
    (hroot : Rooted G r) : Avoiders F r⊆F\G := by
  intro S hS
  obtain ⟨hSF,hrS⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_sdiff.mpr ⟨hSF,fun hSG => hrS (hroot S hSG)⟩

theorem avoiders_card_le_difference (F G : Finset (Finset ℤ)) (r : ℤ)
    (hroot : Rooted G r) : (Avoiders F r).card≤(F\G).card :=
  Finset.card_le_card (avoiders_subset_difference F G r hroot)

theorem avoiders_crooked_of_apRetained (F G : Finset (Finset ℤ)) (r : ℤ)
    (hretain : APRetained F G) (hroot : Rooted G r) :
    ∀ S∈Avoiders F r, ¬IsAP S := by
  intro S hS hAP
  obtain ⟨hSF,hrS⟩ := Finset.mem_filter.mp hS
  exact hrS (hroot S (hretain S hSF hAP))

theorem retained_root_actual_omitter_package
    (Ω : Finset ℤ) (F G : Finset (Finset ℤ)) (r : ℤ)
    (hlegal : Legal Ω F) (hGF : G⊆F) (hne : G.Nonempty)
    (hretain : APRetained F G) (hroot : Rooted G r) :
    r∈Ω ∧ Avoiders F r⊆F\G ∧
      (Avoiders F r).card≤(F\G).card ∧
      ∀ S∈Avoiders F r, ¬IsAP S := by
  exact ⟨retained_root_mem_ground Ω F G r hlegal.1 hGF hne hroot,
    avoiders_subset_difference F G r hroot,
    avoiders_card_le_difference F G r hroot,
    avoiders_crooked_of_apRetained F G r hretain hroot⟩

theorem apRetained_of_crooked_deletion (F E : Finset (Finset ℤ))
    (hE : ∀ S∈E, ¬IsAP S) : APRetained F (F\E) := by
  intro S hSF hAP
  exact Finset.mem_sdiff.mpr ⟨hSF,fun hSE => hE S hSE hAP⟩

theorem avoiders_subset_deletion (F G E : Finset (Finset ℤ)) (r : ℤ)
    (hG : G=F\E) (hroot : Rooted G r) : Avoiders F r⊆E := by
  intro S hS
  obtain ⟨hSF,hrS⟩ := Finset.mem_filter.mp hS
  by_contra hSE
  have hSG : S∈G := by
    rw [hG]
    exact Finset.mem_sdiff.mpr ⟨hSF,hSE⟩
  exact hrS (hroot S hSG)

theorem avoiders_card_le_deletion (F G E : Finset (Finset ℤ)) (r : ℤ)
    (hG : G=F\E) (hroot : Rooted G r) : (Avoiders F r).card≤E.card :=
  Finset.card_le_card (avoiders_subset_deletion F G E r hG hroot)

theorem avoiders_crooked_of_deletion (F G E : Finset (Finset ℤ)) (r : ℤ)
    (hG : G=F\E) (hroot : Rooted G r) (hE : ∀ S∈E, ¬IsAP S) :
    ∀ S∈Avoiders F r, ¬IsAP S := by
  intro S hS
  exact hE S (avoiders_subset_deletion F G E r hG hroot hS)

theorem actual_deletion_root_package
    (Ω : Finset ℤ) (F G E : Finset (Finset ℤ)) (r : ℤ)
    (hlegal : Legal Ω F) (hG : G=F\E) (hne : G.Nonempty)
    (hroot : Rooted G r) (hE : ∀ S∈E, ¬IsAP S) :
    r∈Ω ∧ APRetained F G ∧ Avoiders F r⊆E ∧
      (Avoiders F r).card≤E.card ∧
      ∀ S∈Avoiders F r, ¬IsAP S := by
  have hGF : G⊆F := by rw [hG]; exact Finset.sdiff_subset
  have hretain : APRetained F G := by
    rw [hG]
    exact apRetained_of_crooked_deletion F E hE
  exact ⟨retained_root_mem_ground Ω F G r hlegal.1 hGF hne hroot,
    hretain,avoiders_subset_deletion F G E r hG hroot,
    avoiders_card_le_deletion F G E r hG hroot,
    avoiders_crooked_of_deletion F G E r hG hroot hE⟩

theorem deletion_disjoint (F E : Finset (Finset ℤ)) : Disjoint (F\E) E := by
  apply Finset.disjoint_left.mpr
  intro S hS hSE
  exact (Finset.mem_sdiff.mp hS).2 hSE

theorem deletion_exact_union (F E : Finset (Finset ℤ)) (hEF : E⊆F) :
    (F\E)∪E=F := by
  ext S
  simp only [Finset.mem_union,Finset.mem_sdiff]
  constructor
  · rintro (⟨hSF,_⟩ | hSE)
    · exact hSF
    · exact hEF hSE
  · intro hSF
    by_cases hSE : S∈E
    · exact Or.inr hSE
    · exact Or.inl ⟨hSF,hSE⟩

theorem deletion_card_exact (F E : Finset (Finset ℤ)) (hEF : E⊆F) :
    F.card=(F\E).card+E.card := by
  rw [←Finset.card_union_of_disjoint (deletion_disjoint F E),deletion_exact_union F E hEF]

theorem actual_omitters_le_deletion_bound
    (F G E : Finset (Finset ℤ)) (r : ℤ) (b : ℕ)
    (hG : G=F\E) (hroot : Rooted G r) (hbound : E.card≤b) :
    (Avoiders F r).card≤b :=
  (avoiders_card_le_deletion F G E r hG hroot).trans hbound

#print axioms apRetained_refl
#print axioms apRetained_trans
#print axioms retained_legal
#print axioms retained_root_mem_ground
#print axioms avoiders_subset_difference
#print axioms avoiders_card_le_difference
#print axioms avoiders_crooked_of_apRetained
#print axioms retained_root_actual_omitter_package
#print axioms apRetained_of_crooked_deletion
#print axioms avoiders_subset_deletion
#print axioms avoiders_card_le_deletion
#print axioms avoiders_crooked_of_deletion
#print axioms actual_deletion_root_package
#print axioms deletion_disjoint
#print axioms deletion_exact_union
#print axioms deletion_card_exact
#print axioms actual_omitters_le_deletion_bound
end
end JSP233.KKRetention32
