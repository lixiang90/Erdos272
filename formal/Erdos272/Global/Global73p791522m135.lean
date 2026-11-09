module

public import Erdos272.Global.Global73p96714m134
public import Erdos272.Arithmetic.HalfInterval135
public import Erdos272.Resources.HalfRecovery135

@[expose] public section

namespace JSP233.Global73p791522m135
open StarCompletion
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 73791522≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hhi : 73967140≤N
  · exact Global73p96714m134.actual_original_upper_bound hhi hF
  · have hNhi : N≤73967140 := by omega
    have hNu : N<2^49 := by norm_num; omega
    exact HalfRecovery135.actual_original_upper_of_certificate hN (by omega : N≤74320000) hNu hF
      (HalfInterval135.certificate hN hNhi)

theorem actual_value_eq_B (N : ℕ) (hN : 73791522≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 73791522≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global73p791522m135
