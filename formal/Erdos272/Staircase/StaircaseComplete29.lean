import Erdos272.Staircase.StaircaseTailBridge29
import Erdos272.Foundation.Staircase249
import Erdos272.Foundation.StaircaseThin

/-! Unbounded actual unit-step line bound. The finite square, the two thin
edges, and the actual arithmetic/Abel analytic tail cover all extents. -/
namespace JSP233.StaircaseComplete29
open StaircaseGeometry StaircaseSupply

theorem unbounded_coordinates_defect_le_one {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) :
    ((Family C).card : ℤ) - (PrimitivePool (Family C)).card ≤ 1 := by
  by_cases hL : Height C ≤ 1
  · have hc := StaircaseThin.left_thin_coordinates_card hvalid (fun p hp =>
      (Finset.le_sup (f := Prod.fst) hp).trans hL)
    have hi : ((Family C).card : ℤ) ≤ (PrimitivePool (Family C)).card := by
      exact_mod_cast hc
    omega
  by_cases hR : Width C ≤ 1
  · have hc := StaircaseThin.right_thin_coordinates_card hvalid (fun p hp =>
      (Finset.le_sup (f := Prod.snd) hp).trans hR)
    have hi : ((Family C).card : ℤ) ≤ (PrimitivePool (Family C)).card := by
      exact_mod_cast hc
    omega
  by_cases hB : max (Height C) (Width C) ≤ 249
  · exact Staircase249.original_defect_le_one hvalid
      ((le_max_right _ _).trans hB) ((le_max_left _ _).trans hB)
  · have ht := StaircaseTailBridge29.actual_tail_defect_negative hvalid
      (by omega) (by omega) (by omega)
    omega

theorem actual_family_defect_le_one (F : Finset (Finset ℤ))
    (hF : ∀ S ∈ F, ∃ l r : ℕ, S = Window l r ∧ 4 ≤ S.card) :
    (F.card : ℤ) - (PrimitivePool F).card ≤ 1 := by
  obtain ⟨C,hC,hvalid⟩ := exists_coordinates F hF
  rw [← hC]
  exact unbounded_coordinates_defect_le_one hvalid

theorem actual_family_card_le_pool_add_one (F : Finset (Finset ℤ))
    (hF : ∀ S ∈ F, ∃ l r : ℕ, S = Window l r ∧ 4 ≤ S.card) :
    F.card ≤ (PrimitivePool F).card + 1 := by
  have hi := actual_family_defect_le_one F hF
  omega

#print axioms unbounded_coordinates_defect_le_one
#print axioms actual_family_defect_le_one
#print axioms actual_family_card_le_pool_add_one
end JSP233.StaircaseComplete29
