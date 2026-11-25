module

public import Erdos272.Global.N155716.CommonRoot155716
public import Erdos272.Global.N155716.WindowPayment155716
public import Erdos272.Retention.N155716.Restore155716
public import Erdos272.Global.N158375.Global158375

@[expose] public section

namespace JSP233.Global155716
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 155716 ≤ N) (hhi : N ≤ 158374) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  apply CommonRoot155716.actual_common_root (w := 0) (by decide)
    (by simpa [WindowData155716.info] using hN)
    (by dsimp only [WindowData155716.info]; omega) hF hcard
  intro A hlegal hbad hsize hsparse
  have hb := WindowPayment155716.actual_source_for_proof hN (by omega : N ≤ 161056)
    hlegal hbad (by simpa [WindowData155716.info] using hsize) hsparse (le_refl A)
  simpa only [WindowData155716.G, WindowData155716.Fee, WindowData155716.CoeffA,
    WindowData155716.CoeffB, WindowData155716.CoeffC,
    SourceData155716W0.G, SourceData155716W0.SourceUpper, SourceData155716W0.CoeffA,
    SourceData155716W0.CoeffB, SourceData155716W0.CoeffC] using hb

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 155716 ≤ N) (hhi : N ≤ 158374) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation155716.actual_initial_preparation hN (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore155716.actual_recovered_original hg hN (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 155716 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 158375 ≤ N
  · exact Global158375.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 158374 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 155716 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 155716 ≤ N) :
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
end JSP233.Global155716
