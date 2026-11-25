module

public import Erdos272.Core.N67702.FixedAnchorSmall67702
public import Erdos272.Counting.N65172.Small77Pierce65172
public import Erdos272.Counting.N65172.Small77Packing65172

@[expose] public section

namespace JSP233.SmallCredit65172
open StarCompletion SparseSmall39 SmallKernel112 Small77Kernel65172
open Small77Rank65172 Small77Pierce65172 Small77Packing65172
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem credit_or_thin {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅) :
    (F.card : ℝ)≤5779*(N : ℝ)-231312 ∨
      ((∀S∈F,77≤S.card) ∧ (Small F 77).card≤N*(N-1)/5852) := by
  by_cases h76 : (Small F 76).Nonempty
  · left
    have hb:=FixedAnchorSmall67702.actual_fixed_anchor_small_credit (L:=77) (T:=76)
      (by decide) (by decide) (by omega) (by omega) hlegal hbad h76 hkernel
    norm_num [FixedSmallScalars82427.Coefficient,FixedSmallScalars82427.Credit,
      Nat.choose_two_right] at hb
    nlinarith only [hb,Nat.cast_nonneg (α:=ℝ) N]
  have hmin : ∀S∈F,77≤S.card := by
    intro S hS
    by_contra hn
    exact h76 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
  let H:=Small F 77
  have hHF : H⊆F := Finset.filter_subset _ _
  have hcard : ∀S∈H,S.card=77 := by
    intro S hS
    have hl:=hmin S (hHF hS)
    have hh:=(Finset.mem_filter.mp hS).2
    omega
  have hlegalH:=legal_sub hlegal hHF
  have hbadH : ∀S∈H,¬IsAP S := fun S hS=>hbad S (hHF hS)
  by_cases hmid : ∃A∈H,∃B∈H,A≠B ∧ 2≤(A∩B).card ∧ (A∩B).card≤75
  · left
    obtain ⟨A,hA,B,hB,_hne,hlo,hhi⟩ := hmid
    exact moderate_credit (by omega) hlegal hbad hkernel
      (hHF hA) (hHF hB) (hcard A hA) (hcard B hB) hlo hhi
  have hlarge : ∀A∈H,∀B∈H,A≠B→2≤(A∩B).card→(A∩B).card=76 := by
    intro A hA B hB hne hlo
    have hu:=inter_le (hcard A hA) (hcard B hB) hne
    by_contra hn
    exact hmid ⟨A,hA,B,hB,hne,hlo,by omega⟩
  by_cases hpierce : ∃A∈H,∃B∈H,A≠B ∧ (A∩B).card=76 ∧ ∃T∈H,(T∩(A∩B)).card=1
  · left
    obtain ⟨A,hA,B,hB,hne,hAB,T,hT,hTP⟩ := hpierce
    exact pierced_credit (by omega) hlegal hbad hkernel (hHF hA) (hHF hB) (hHF hT) hne
      (hcard A hA) (hcard B hB) (hcard T hT) hAB hTP
  right
  refine ⟨hmin,?_⟩
  have hnoone : ∀A∈H,∀B∈H,A≠B→(A∩B).card=76→∀T∈H,(T∩(A∩B)).card≠1 := by
    intro A hA B hB hne hAB T hT hTP
    exact hpierce ⟨A,hA,B,hB,hne,hAB,T,hT,hTP⟩
  exact thin_of_no_witnesses (by omega) hlegalH hbadH hcard hkernel hlarge hnoone

#print axioms credit_or_thin
end
end JSP233.SmallCredit65172
