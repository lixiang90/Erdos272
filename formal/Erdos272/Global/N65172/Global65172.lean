module

public import Erdos272.Counting.N65968.ImportProbe65968
public import Erdos272.Counting.N65968.IntegerFeePilot65968
public import Erdos272.Global.N65172.CommonRoot65172
public import Erdos272.Global.N65172.WindowPayment65172
public import Erdos272.Global.N65172.InitialPreparation65172
public import Erdos272.Retention.N65968.Restore65968
public import Erdos272.Global.N65968.Global65968

@[expose] public section

namespace JSP233.Global65172
open StarCompletion APGeometry DenseDeletion40 WindowData65172
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172 ≤ N) (hhi : N ≤ 65967) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  apply CommonRoot65172.actual_common_root hN hhi hF hcard
  intro w hw hlo hupper A hlegal hbad hsize hsparse hAF hwitness
  exact WindowPayment65172.actual_source_for_proof hw hlo hupper
    hlegal hbad hsize hsparse hF hAF hwitness

theorem actual_rooted_upper {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172 ≤ N) (hhi : N ≤ 65967) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) : F.card ≤ B N := by
  rcases InitialPreparation65172.actual_initial_preparation (by omega) (by omega) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H, c, L, R, P, T, _hHF, hcardH, hg⟩ := hstart
    have hb := Restore65968.actual_recovered_original hg (by omega) (by omega)
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172 ≤ N) (hF : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases hlarge : 65968 ≤ N
  · exact Global65968.actual_original_upper_bound hlarge hF
  by_cases hcard : B N ≤ F.card
  · have hhi : N ≤ 65967 := by omega
    exact actual_rooted_upper hN hhi hF hcard (actual_closed_root hN hhi hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 65172 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 65172 ≤ N) :
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
end JSP233.Global65172
