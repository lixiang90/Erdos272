module

public import Erdos272.Global.N150465.CommonRoot150465
public import Erdos272.Global.N150465.WindowPayment150465
public import Erdos272.Retention.N150465.Restore150465
public import Erdos272.Global.N151879.Global151879

@[expose] public section

namespace JSP233.Global150465
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 150465 ≤ N) (hhi : N ≤ 151878) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  apply CommonRoot150465.actual_common_root (w := 0) (by decide)
    (by simpa [WindowData150465.info] using hN)
    (by dsimp only [WindowData150465.info]; omega) hF hcard
  intro A hlegal hbad hsize hsparse
  have hb := WindowPayment150465.actual_source_for_proof hN (by omega : N ≤ 153079)
    hlegal hbad (by simpa [WindowData150465.info] using hsize) hsparse (le_refl A)
  simpa only [WindowData150465.G, WindowData150465.Fee, WindowData150465.CoeffA,
    WindowData150465.CoeffB, WindowData150465.CoeffC,
    SourceData150465W0.G, SourceData150465W0.SourceUpper, SourceData150465W0.CoeffA,
    SourceData150465W0.CoeffB, SourceData150465W0.CoeffC] using hb

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 150465 ≤ N) (hhi : N ≤ 151878) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation150465.actual_initial_preparation (by omega) (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore150465.actual_recovered_original hg (by omega) (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 150465 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 151879 ≤ N
  · exact Global151879.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 151878 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 150465 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 150465 ≤ N) :
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
end JSP233.Global150465
