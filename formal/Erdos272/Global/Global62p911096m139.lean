module

public import Erdos272.Global.Global63p917403m138
public import Erdos272.Arithmetic.HalfInterval139
public import Erdos272.Resources.HalfRecovery139

@[expose] public section

namespace JSP233.Global62p911096m139
open StarCompletion
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 62911096≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hhi : 63917403≤N
  · exact Global63p917403m138.actual_original_upper_bound hhi hF
  · have hNhi : N≤63917403 := by omega
    have hNu : N<2^49 := by norm_num; omega
    exact HalfRecovery139.actual_original_upper_of_certificate hN hNhi hNu hF
      (HalfInterval139.certificate hN hNhi)

theorem actual_value_eq_B (N : ℕ) (hN : 62911096≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 62911096≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global62p911096m139
