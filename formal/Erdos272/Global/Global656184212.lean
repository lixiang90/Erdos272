import Erdos272.Global.Global659912209
import Erdos272.Global.PaddedCommon212
import Erdos272.Resources.RootedWindow212

namespace JSP233.Global656184212
open StarCompletion
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 656184≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hlarge : 659912≤N
  · exact Global659912209.actual_original_upper_bound hlarge hF
  · by_cases hc : B N≤F.card
    · have hroot := PaddedCommon212.actual_closed_root (by omega : 655996≤N)
        (by omega : N≤659912) hF hc
      exact RootedWindow212.actual_original_upper_of_root11 hN (by omega) hF hroot
    · omega

theorem actual_value_eq_B (N : ℕ) (hN : 656184≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 656184≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global656184212
