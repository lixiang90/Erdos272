module

public import Erdos272.Global.N130000.CommonRoot130000
public import Erdos272.Global.N130000.WindowPayment130000
public import Erdos272.Retention.N142758.Restore142758
public import Erdos272.Global.N142758.Global142758

@[expose] public section

namespace JSP233.Global130000
open StarCompletion APGeometry DenseDeletion40 WindowData130000
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root_for_window {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  have hg := WindowGates130000.gates (by omega : w < 4)
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  apply CommonRoot130000.actual_common_root hw hlo hhi hF hcard
  · intro A hlegal hbad hsize hsparse
    exact WindowPayment130000.actual_source_for_proof (by omega : w < 4)
      hlo hhi hlegal hbad hsize hsparse (le_refl A)
  · intro A hlegal hbad hsize hsparse
    exact WindowPayment130000.actual_source_for_proof (w := 3) (by decide)
      (by simpa only [info] using hN) (by simpa only [info] using hNhi)
      hlegal hbad hsize hsparse (le_refl A)

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 130000 ≤ N) (hhi : N ≤ 142757) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  by_cases hlow : N ≤ 132797
  · exact actual_closed_root_for_window (w := 0) (by decide)
      (by change 130000 ≤ N; omega) (by change N ≤ 132797; omega) hF hcard
  by_cases hmiddle : N ≤ 137732
  · exact actual_closed_root_for_window (w := 1) (by decide)
      (by change 132798 ≤ N; omega) (by change N ≤ 137732; omega) hF hcard
  · exact actual_closed_root_for_window (w := 2) (by decide)
      (by change 137733 ≤ N; omega) (by change N ≤ 145304; omega) hF hcard

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 130000 ≤ N) (hhi : N ≤ 142757) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation150465.actual_initial_preparation (by omega) (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore142758.actual_recovered_original hg (by omega) (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 130000 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 142758 ≤ N
  · exact Global142758.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 142757 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 130000 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 130000 ≤ N) :
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
end JSP233.Global130000
