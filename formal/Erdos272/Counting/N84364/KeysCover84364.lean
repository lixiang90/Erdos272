module

public import Erdos272.Counting.N84364.KeysOrder84364

@[expose] public section

namespace JSP233.KeysCover84364
open StarCompletion SharpSmall212
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_bucket_cover_card {N : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hA : A∈F) (hAN : A.Nonempty) (upper : Bool) :
    F.card≤∑ x ∈ A, (Bucket F A x upper).card := by
  have hcover : F⊆A.biUnion (fun x => Bucket F A x upper) := by
    intro S hS
    have hSA : (S∩A).Nonempty := by
      by_cases he : S=A
      · simpa only [he, Finset.inter_self] using hAN
      · exact isAP_nonempty (hlegal.2 S hS A hA he)
    have hex : ∃ x ∈ S∩A, ∀ y ∈ S∩A, Order upper x y := by
      cases upper
      · simpa only [Order, Bool.false_eq_true, ↓reduceIte] using
          Finset.exists_min_image (S∩A) (fun z : ℤ => z) hSA
      · simpa only [Order, ↓reduceIte] using
          Finset.exists_max_image (S∩A) (fun z : ℤ => z) hSA
    obtain ⟨x, hx, hmin⟩ := hex
    obtain ⟨hxS, hxA⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_biUnion.mpr ⟨x, hxA, Finset.mem_filter.mpr
      ⟨hS, hxS, fun y hyS hyA => hmin y (Finset.mem_inter.mpr ⟨hyS, hyA⟩)⟩⟩
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)

#print axioms actual_bucket_cover_card
end
end JSP233.KeysCover84364
