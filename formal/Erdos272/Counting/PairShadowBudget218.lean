import Erdos272.Counting.WitnessInterval43
import Erdos272.Counting.APCount41
import Mathlib.Data.Finset.Powerset

/-! The private pairs of all actual root-crooked members and the entire
pair shadow of any actual root-AP subfamily use one physical pair pool. -/
namespace JSP233.PairShadowBudget218
open StarCompletion APGeometry APCount41 WitnessInterval43 LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def RootUnitAP (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F.filter fun S => c∈S ∧ IsAP S ∧ 2≤S.card ∧ Step S=1

def PairShadow (U : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  U.biUnion fun P => (P.erase c).powersetCard 2

theorem actual_pair_shadow_capacity {Ω : Finset ℤ}
    {F U : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal Ω F) (hUF : U⊆F)
    (hrootU : ∀P∈U,c∈P) (hAPU : ∀P∈U,IsAP P) :
    (RootCrooked F c).card+(PairShadow U c).card ≤ (Ω.erase c).card.choose 2 := by
  let C := RootCrooked F c
  let X := {S // S∈C}
  have hCF : C⊆F := Finset.filter_subset _ _
  have hc : ∀S∈C,c∈S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hbad : ∀S∈C,¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.2
  have hex : ∀S:X,∃Q,IntrinsicPair c S.val Q := fun S =>
    actual_intrinsic_pair_exists (hc S.val S.property) (hbad S.val S.property)
  choose Q hQ using hex
  let I := (Finset.univ : Finset X).image Q
  have hi : Function.Injective Q := by
    intro S T he
    apply Subtype.ext
    exact actual_intrinsic_member_eq hF (hCF S.property) (hCF T.property)
      (hc S.val S.property) (hc T.val T.property) (hQ S)
      (by rw [he]; exact (hQ T).2.2.1)
  have hI : I.card=C.card := by
    simp only [I, Finset.card_image_of_injective _ hi, Finset.card_univ,
      Fintype.card_coe, X]
  have hd : Disjoint I (PairShadow U c) := by
    apply Finset.disjoint_left.mpr
    intro W hWI hWU
    obtain ⟨S, _hS, rfl⟩ := Finset.mem_image.mp hWI
    obtain ⟨P, hPU, hQP⟩ := Finset.mem_biUnion.mp hWU
    apply witness_pair_not_subset_AP_member hF (hCF S.property) (hUF hPU)
      (hc S.val S.property) (hrootU P hPU) (hbad S.val S.property) (hAPU P hPU) (hQ S)
    exact (Finset.mem_powersetCard.mp hQP).1.trans (Finset.erase_subset _ _)
  have hIsub : I⊆(Ω.erase c).powersetCard 2 := by
    intro W hWI
    obtain ⟨S, _hS, rfl⟩ := Finset.mem_image.mp hWI
    refine Finset.mem_powersetCard.mpr ⟨?_, (hQ S).1⟩
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact (hQ S).2.1 (he ▸ hx),
        hF.1 S.val (hCF S.property) ((hQ S).2.2.1 hx)⟩
  have hUsub : PairShadow U c⊆(Ω.erase c).powersetCard 2 := by
    intro W hWU
    obtain ⟨P, hPU, hWP⟩ := Finset.mem_biUnion.mp hWU
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hWP
    refine Finset.mem_powersetCard.mpr ⟨?_, hcard⟩
    intro x hx
    obtain ⟨hxc, hxP⟩ := Finset.mem_erase.mp (hsub hx)
    exact Finset.mem_erase.mpr ⟨hxc, hF.1 P (hUF hPU) hxP⟩
  have hcap := Finset.card_le_card (Finset.union_subset hIsub hUsub)
  rw [Finset.card_union_of_disjoint hd, hI, Finset.card_powersetCard] at hcap
  exact hcap

theorem actual_root_unit_pair_capacity {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} {c : ℤ} (hF : Legal Ω F) :
    (RootCrooked F c).card+(PairShadow (RootUnitAP F c) c).card ≤
      (Ω.erase c).card.choose 2 := by
  apply actual_pair_shadow_capacity hF (Finset.filter_subset _ _)
  · intro P hP
    exact (Finset.mem_filter.mp hP).2.1
  · intro P hP
    exact (Finset.mem_filter.mp hP).2.2.1

theorem actual_ground_root_unit_pair_capacity {N : ℕ}
    {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    (RootCrooked F c).card+(PairShadow (RootUnitAP F c) c).card ≤ (N-1).choose 2 := by
  have hh := actual_root_unit_pair_capacity (c := c) hF
  simpa only [Finset.card_erase_of_mem hc, ground_card] using hh

#print axioms actual_pair_shadow_capacity
#print axioms actual_root_unit_pair_capacity
#print axioms actual_ground_root_unit_pair_capacity
end
end JSP233.PairShadowBudget218
