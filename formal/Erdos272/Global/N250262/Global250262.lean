module

public import Erdos272.Global.N250262.CommonRoot250262
public import Erdos272.Retention.N250262.Restore250262
public import Erdos272.Global.N291012.Global291012

@[expose] public section

namespace JSP233.Global250262
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 250262 ≤ N) (hhi : N ≤ 291011) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  obtain ⟨w, hw, hlo, hhigh⟩ := WindowData250262.cover hN hhi
  exact CommonRoot250262.actual_common_root hw hlo hhigh hF hcard

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 250262 ≤ N) (hhi : N ≤ 291011) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation250262.actual_initial_preparation hN (by omega : N ≤ 642498) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore250262.actual_recovered_original hg hN hhi
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 250262 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 291012 ≤ N
  · exact Global291012.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 291011 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 250262 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 250262 ≤ N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card = B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card ≤ F.card := by
  obtain ⟨F, hF, hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F, hF, hcard, fun G hG => by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_closed_root
#print axioms actual_rooted_upper
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global250262
