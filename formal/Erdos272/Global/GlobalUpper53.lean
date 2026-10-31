import Erdos272.Counting.MiddleDeficit52
import Erdos272.Retention.JointFringe44
import Erdos272.Construction.ExtremalValue45
import Erdos272.Global.EndpointStability53
import Erdos272.Global.NonInterval53

/-! Actual original-family upper bound in the large-N range. The retained
family and its reflected orientation are always those of the original family.
The same root and exterior envelope are used for stability and restoration. -/
namespace JSP233.GlobalUpper53
open StarCompletion APGeometry DenseDeletion40 FamilyReflect43
open MiddleDeficit52 LongTerminal35
open EndpointStability53
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

theorem actual_deleted_long_core_restore28 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hgeometry : 812*(L+N-R)≤N) (hF : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 28 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 28 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  apply JointFringe44.actual_long_core_restore 28 29 N c L R F
    (Retained N 28 F) (Deleted N 28 F)
    (by decide) (by decide) (by decide)
    ((by norm_num : 29^3≤(2:ℕ)^49).trans hN) hc hcL hLR hRN hthin
    (by simpa only [show 28*29=812 by norm_num,show 29-28=1 by norm_num,one_mul] using hgeometry)
    ?_ rfl (actual_deleted_subset N 28 F) hF
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2) hne hi
  have hj : JointFringe44.JointCount 29=131 := by decide
  rw [hj]
  omega

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_contra hn
  have hcounter : B N<F.card := by omega
  obtain ⟨H,_hHF,hLH,hcard,_hD,_hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,_hT,henv,
    _hsq,h812,h6,h32,hJ3⟩ := actual_original_prepared_payments28 hN hF hcounter
  have hcounterH : B N<H.card := by omega
  have hnear := CrossStartup47.actual_retained_near_counter28 hN hLH hcounterH
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by have hh:=Finset.mem_Icc.mp hc;omega)
  have hlow : ∀S∈Avoiders (Retained N 28 H) (c:ℤ),∃a∈S,a≤(L:ℤ) := by
    intro S hS
    obtain ⟨a,ha,haL,_⟩ := (henv S hS).1
    exact ⟨a,ha,haL⟩
  have hright : ∀S∈Avoiders (Retained N 28 H) (c:ℤ),∃b∈S,(R:ℤ)≤b := by
    intro S hS
    obtain ⟨b,hb,hRb,_⟩ := (henv S hS).2
    exact ⟨b,hb,hRb⟩
  have hi := NonInterval53.actual_avoiders_intervals (δ:=3138)
    (by norm_num at hN;omega : 6≤N)
    (Nat.lt_pow_succ_log_self (by decide : 1<2) N) hcG (actual_retained_legal hLH)
    hroot hLc hLR hRN hlow hright h32 hJ3 (by norm_num at hN;omega) hnear
  obtain ⟨P,hPG,_hPL⟩ := hP
  have hb := actual_deleted_long_core_restore28 hN (Finset.mem_Icc.mp hc).1
    hLc hLR hRN h6 h812 hLH ⟨P,hPG⟩ hi
  omega

theorem actual_value_eq_B (N : ℕ) (hN : 2^49≤N) : ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by norm_num at hN;omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 2^49≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by norm_num at hN;omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_deleted_long_core_restore28
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.GlobalUpper53
