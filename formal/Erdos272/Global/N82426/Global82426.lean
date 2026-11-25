module

public import Erdos272.Counting.N82426.PointCommon82426
public import Erdos272.Counting.N82426.PointPreparation82426
public import Erdos272.Retention.N82426.PointRecovery82426
public import Erdos272.Global.N82427.Global82427

@[expose] public section

namespace JSP233.Global82426
open StarCompletion APGeometry DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_closed_root {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card) :
    ∃ c∈Ground 82426, ∀ S∈Retained 82426 12 F, ¬IsAP S→c∈S :=
  PointCommon82426.actual_common_root hF hcard

theorem actual_rooted_upper {F : Finset (Finset ℤ)}
    (hF : Legal (Ground 82426) F) (hcard : B 82426≤F.card)
    (hroot : ∃ c∈Ground 82426, ∀ S∈Retained 82426 12 F, ¬IsAP S→c∈S) :
    F.card≤B 82426 := by
  rcases PointPreparation82426.actual_initial_preparation (by decide : 82426≤82426)
    (by decide : 82426≤179999) hF hcard hroot with hpaid | hstart
  · exact hpaid
  · obtain ⟨H,c,L,R,P,T,_hHF,hcardH,hg⟩ := hstart
    have hb := PointRecovery82426.actual_recovered_original hg
    omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82426≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hlarge : 82427≤N
  · exact Global82427.actual_original_upper_bound hlarge hF
  have heq : N=82426 := by omega
  subst N
  by_cases hcard : B 82426≤F.card
  · exact actual_rooted_upper hF hcard (actual_closed_root hF hcard)
  · omega

theorem actual_value_eq_B (N : ℕ) (hN : 82426≤N) : ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 82426≤N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card=B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG => by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_closed_root
#print axioms actual_rooted_upper
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global82426
