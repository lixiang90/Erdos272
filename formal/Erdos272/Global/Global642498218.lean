import Erdos272.Global.Global653292214
import Erdos272.Global.Common240218
import Erdos272.Resources.PaddedUnit240218
import Erdos272.Global.Rooted642498218

/-! Same-family pair-shadow recovery joins the closed minimum240 common-root
entry.  All actual source, density, geometry and terminal facts are internal. -/
namespace JSP233.Global642498218
open StarCompletion DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 642498≤N) (hhigh : N≤653292)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  have hp := PaddedUnit240218.actual_price hN hhigh
  exact Common240218.actual_common_root (g := Unit240Rows218.G) (u := 0) (eta := 0)
    (light := Unit240Aggregate218.Fee) hN (by omega) hF hcard
    (by norm_num [Unit240Rows218.G])
    (PaddedUnit240218.actual_fees (by omega) hF) hp.1
    (by simpa only [zero_add] using hp.2)

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 642498≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hlarge : 653292≤N
  · exact Global653292214.actual_original_upper_bound hlarge hF
  · by_cases hcard : B N≤F.card
    · have hroot := actual_closed_root hN (by omega) hF hcard
      exact Rooted642498218.actual_rooted_upper hN (by omega) hF hroot
    · omega

theorem actual_value_eq_B (N : ℕ) (hN : 642498≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 642498≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_closed_root
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global642498218
