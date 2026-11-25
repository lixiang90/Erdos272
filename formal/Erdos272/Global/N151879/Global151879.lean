module

public import Erdos272.Global.N151879.CommonRoot151879
public import Erdos272.Global.N151879.WindowPayment151879
public import Erdos272.Retention.N153080.Restore153080
public import Erdos272.Global.N153080.Global153080

@[expose] public section

namespace JSP233.Global151879
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 151879 ≤ N) (hhi : N ≤ 153079) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  apply CommonRoot151879.actual_common_root (w := 0) (by decide)
    (by simpa [WindowData151879.info] using hN)
    (by dsimp only [WindowData151879.info]; omega) hF hcard
  intro A hlegal hbad hsize hsparse
  have hb := WindowPayment151879.actual_source_for_proof hN (by omega : N ≤ 153079)
    hlegal hbad (by simpa [WindowData151879.info] using hsize) hsparse (le_refl A)
  simpa only [WindowData151879.G, WindowData151879.Fee, WindowData151879.CoeffA,
    WindowData151879.CoeffB, WindowData151879.CoeffC,
    SourceData151879W0.G, SourceData151879W0.SourceUpper, SourceData151879W0.CoeffA,
    SourceData151879W0.CoeffB, SourceData151879W0.CoeffC] using hb

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 151879 ≤ N) (hhi : N ≤ 153079) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation153080.actual_initial_preparation (by omega) (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore153080.actual_recovered_original hg (by omega) (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 151879 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 153080 ≤ N
  · exact Global153080.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 153079 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 151879 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 151879 ≤ N) :
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
end JSP233.Global151879
