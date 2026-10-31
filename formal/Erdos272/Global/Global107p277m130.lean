import Erdos272.Global.CroftKernel113
import Erdos272.Global.OriginalPrepare130
import Erdos272.Global.GlobalUpper53

/-! The original-family bound for N >= 107277000. The root and recovery
lemmas cover the whole interval below 2^49; the simpler theorem supplies the tail. -/
namespace JSP233.Global107p277m130
open StarCompletion
open scoped Classical
noncomputable section

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 107277000 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hhi : 2^49 ≤ N
  · exact GlobalUpper53.actual_original_upper_bound hhi hF
  · have hNu : N < 2^49 := lt_of_not_ge hhi
    by_contra hn
    have hcard : B N ≤ F.card := by omega
    have hroot := CroftKernel113.actual_original_root11 (N:=N) (F:=F) (by omega) hNu hF hcard
    have hb := OriginalPrepare130.actual_original_upper_of_root11 hN hNu hF hroot
    omega

theorem actual_value_eq_B (N : ℕ) (hN : 107277000 ≤ N) :
    ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 107277000 ≤ N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card = B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card ≤ F.card := by
  obtain ⟨F, hF, hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F, hF, hcard, fun G hG => by
    simpa only [hcard] using actual_original_upper_bound hN hG⟩

#check @actual_original_upper_bound
#check @actual_value_eq_B
#check @actual_optimal_family
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global107p277m130
