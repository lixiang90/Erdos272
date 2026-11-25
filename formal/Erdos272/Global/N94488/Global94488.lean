module

public import Erdos272.Global.N94488.CommonRoot94488
public import Erdos272.Global.N94488.WindowPayment94488
public import Erdos272.Global.N94488.InitialPreparation94488
public import Erdos272.Retention.N94488.Restore94488
public import Erdos272.Global.N109474.Global109474

@[expose] public section

namespace JSP233.Global94488
open StarCompletion APGeometry DenseDeletion40 WindowData94488
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root_for_window {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 5) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  have hg := WindowGates94488.gates (by omega : w < 6)
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  apply CommonRoot94488.actual_common_root hw hlo hhi hF hcard
  · intro A hlegal hbad hsize hsparse
    exact WindowPayment94488.actual_source_for_proof (by omega : w < 6)
      hlo hhi hlegal hbad hsize hsparse (le_refl A)
  · intro A hlegal hbad hsize hsparse
    exact WindowPayment94488.actual_source_for_proof (w := 5) (by decide)
      (by simpa only [info] using hN) (by simpa only [info] using hNhi)
      hlegal hbad hsize hsparse (le_refl A)

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 94488 ≤ N) (hhi : N ≤ 109473) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  by_cases h0 : N ≤ 96560
  · exact actual_closed_root_for_window (w := 0) (by decide)
      (by change 94488 ≤ N; omega) (by change N ≤ 96560; omega) hF hcard
  by_cases h1 : N ≤ 98656
  · exact actual_closed_root_for_window (w := 1) (by decide)
      (by change 96561 ≤ N; omega) (by change N ≤ 98656; omega) hF hcard
  by_cases h2 : N ≤ 100774
  · exact actual_closed_root_for_window (w := 2) (by decide)
      (by change 98657 ≤ N; omega) (by change N ≤ 100774; omega) hF hcard
  by_cases h3 : N ≤ 105079
  · exact actual_closed_root_for_window (w := 3) (by decide)
      (by change 100775 ≤ N; omega) (by change N ≤ 105079; omega) hF hcard
  exact actual_closed_root_for_window (w := 4) (by decide)
      (by change 105080 ≤ N; omega) (by change N ≤ 109473; omega) hF hcard

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 94488 ≤ N) (hhi : N ≤ 109473) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation94488.actual_initial_preparation (by omega) (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore94488.actual_recovered_original hg (by omega) (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 94488 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 109474 ≤ N
  · exact Global109474.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 109473 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 94488 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 94488 ≤ N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card = B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card ≤ F.card := by
  obtain ⟨F, hF, hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F, hF, hcard, fun G hG => by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_closed_root_for_window
#print axioms actual_closed_root
#print axioms actual_rooted_upper
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global94488
