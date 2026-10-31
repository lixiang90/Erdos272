import Erdos272.Global.APPrepare49
import Erdos272.Counting.ShortAP208

/-! Preserve the actual preparation filters, including the no-high-witness
family, while replacing the short-progression count by its sharp linear
bound. No numerical endpoint-library or no-high-witness estimate is assumed. -/
namespace JSP233.ActualPreparation208
open StarCompletion APGeometry APPrepare49 PreparedWitness48
open PrivatePairExistence
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_preparation_count {N : ℕ} {F : Finset (Finset ℤ)} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬ IsAP S → c ∈ S) :
    F.card ≤ (PreparedCrooked F c L).card + (PreparedAP F c L).card + N +
      (CrookedMembers F \ HighMembers F c L).card + (LowCut F c).card +
      (HighCut F c L).card + (SmallAP F).card := by
  let D := (HighMembers F c L).filter (fun S => BoundaryWitness S c L)
  have hDF : D ⊆ F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).1
  have hD : D.card ≤ N := actual_division_point_witness_card hF hDF
    (fun S hS => hroot S (hDF hS)
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hHsub : HighMembers F c L ⊆ CrookedMembers F := Finset.filter_subset _ _
  have hp := Finset.card_sdiff_add_card_eq_card hHsub
  have hq := Finset.card_filter_add_card_filter_not (s := HighMembers F c L)
    (fun S => BoundaryWitness S c L)
  change D.card + (PreparedCrooked F c L).card = (HighMembers F c L).card at hq
  obtain ⟨h1, h2, h3⟩ := actual_AP_filter_partitions F c L
  have h4 := actual_progression_crooked_partition F
  omega

theorem actual_small_AP_cut_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 19 ≤ N) (hF : Legal (Ground N) F) :
    (SmallAP F).card ≤ 2 * N - 1 := by
  have hsub : SmallAP F ⊆ F := fun S hS => (actual_small_AP_member hS).1
  have hlegal : Legal (Ground N) (SmallAP F) :=
    ⟨fun S hS => hF.1 S (hsub hS),
     fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
  exact ShortAP208.actual_small_AP_family_count hN hlegal
    (fun S hS => (actual_small_AP_member hS).2.1)
    (fun S hS => (actual_small_AP_member hS).2.2)

theorem actual_preparation_count_short {N : ℕ} {F : Finset (Finset ℤ)} {c L : ℤ}
    (hN : 19 ≤ N) (hF : Legal (Ground N) F)
    (hroot : ∀ S ∈ F, ¬ IsAP S → c ∈ S) :
    F.card ≤ (PreparedCrooked F c L).card + (PreparedAP F c L).card + 3 * N +
      (CrookedMembers F \ HighMembers F c L).card + (LowCut F c).card +
      (HighCut F c L).card := by
  have hp := actual_preparation_count (L := L) hF hroot
  have hs := actual_small_AP_cut_count hN hF
  omega

#print axioms actual_preparation_count
#print axioms actual_small_AP_cut_count
#print axioms actual_preparation_count_short
end
end JSP233.ActualPreparation208
