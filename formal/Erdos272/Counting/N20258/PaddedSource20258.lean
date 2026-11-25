module

public import Erdos272.Counting.Density41
public import Erdos272.Geometry.N20258.TranslatedPool20258
public import Erdos272.Foundation.PrivatePairExistence

@[expose] public section
/-! The sparse cutoff is taken in the paid ambient U. The family, its
cardinality, and the pool of each individual member survive translation.
The remaining crooked members are charged exactly once. -/
namespace JSP233.PaddedSource20258
open StarCompletion AffineLine30 IntrinsicTriples208 Density41 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

def mass (G : Finset (Finset ℤ)) : ℝ := ∑ S ∈ G, ((Pool S).card : ℝ)

theorem mass_map (G : Finset (Finset ℤ)) (c d : ℤ) (hd : 0 < d) :
    mass (mapFamily c d G) = mass G := by
  unfold mass mapFamily
  rw [Finset.sum_image (fun _ _ _ _ he => mapSet_injective c d hd he)]
  apply Finset.sum_congr rfl
  intro S _
  rw [TranslatedPool20258.pool_map c d hd, mapFamily_card c d hd]

theorem sparse_map (G : Finset (Finset ℤ)) (U r : ℕ) (c d : ℤ) (hd : 0 < d) :
    SparseCrooked U r (mapFamily c d G) = mapFamily c d (SparseCrooked U r G) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hG,hbad,hsize⟩ := actual_sparse_membership.mp hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hG
    rw [mapSet_card c d hd] at hsize
    exact Finset.mem_image.mpr ⟨S,actual_sparse_membership.mpr
      ⟨hS,fun h => hbad (affine_isAP c d hd h),hsize⟩,rfl⟩
  · intro hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hG,hbad,hsize⟩ := actual_sparse_membership.mp hS
    exact actual_sparse_membership.mpr ⟨Finset.mem_image.mpr ⟨S,hG,rfl⟩,
      fun h => hbad ((affine_isAP_iff c d hd S).mp h),by simpa only [mapSet_card c d hd] using hsize⟩

theorem source_pullback {U r : ℕ} {F : Finset (Finset ℤ)} {c d : ℤ} (hd : 0 < d) {h Z : ℝ}
    (paid : h*((SparseCrooked U r (mapFamily c d F)).card : ℝ) ≤
      mass (SparseCrooked U r (mapFamily c d F))+Z) :
    h*((SparseCrooked U r F).card : ℝ) ≤ mass (SparseCrooked U r F)+Z := by
  simpa only [sparse_map F U r c d hd, mapFamily_card c d hd, mass_map _ c d hd] using paid

/-- Add the crooked members above the sparse cutoff to a paid source. -/
theorem crooked_payment {U r : ℕ} {F : Finset (Finset ℤ)} {x h Z : ℝ}
    (paid : h*((SparseCrooked U r F).card : ℝ) ≤ mass (SparseCrooked U r F)+Z)
    (dense : ∀ S ∈ F, ¬IsAP S → U < r*S.card → x ≤ ((Pool S).card : ℝ)) :
    x*((CrookedMembers F).card : ℝ) ≤ (x-h)*((SparseCrooked U r F).card : ℝ)+mass F+Z := by
  let H := CrookedMembers F
  let G := SparseCrooked U r F
  let D := H \ G
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hGH : G ⊆ H := by
    intro S hS
    obtain ⟨hF,hbad,_⟩ := actual_sparse_membership.mp hS
    exact Finset.mem_filter.mpr ⟨hF,hbad⟩
  have card : D.card + G.card = H.card := Finset.card_sdiff_add_card_eq_card hGH
  have sum : mass D + mass G = mass H := Finset.sum_sdiff hGH
  have whole : mass H ≤ mass F :=
    Finset.sum_le_sum_of_subset_of_nonneg hHF (fun _ _ _ => by positivity)
  have cost : x*(D.card : ℝ) ≤ mass D := by
    calc
      _ = ∑ _S ∈ D, x := by simp [mul_comm]
      _ ≤ mass D := by
        apply Finset.sum_le_sum
        intro S hS
        obtain ⟨hH,hnot⟩ := Finset.mem_sdiff.mp hS
        obtain ⟨hF,hbad⟩ := Finset.mem_filter.mp hH
        exact dense S hF hbad (lt_of_not_ge (fun h => hnot (actual_sparse_membership.mpr ⟨hF,hbad,h⟩)))
  have cardR : (D.card : ℝ)+G.card = H.card := by exact_mod_cast card
  change h*(G.card : ℝ) ≤ mass G+Z at paid
  change x*(H.card : ℝ) ≤ (x-h)*G.card+mass F+Z
  rw [← cardR]
  linarith only [cost, paid, sum, whole]

end
end JSP233.PaddedSource20258
