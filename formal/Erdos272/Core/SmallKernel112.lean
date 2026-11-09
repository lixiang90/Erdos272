module

public import Erdos272.Global.RootBranch112

@[expose] public section

/-! A small empty kernel pays the whole actual family, including all Large.
The chosen minimum member is an actual member of the original family.
-/
namespace JSP233.SmallKernel112
open StarCompletion SparseSmall39 RootBranch112
open scoped Classical BigOperators
noncomputable section

def Small (F : Finset (Finset ℤ)) (L : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => S.card≤L)

theorem actual_member_nonempty_of_two {N : ℕ} {F : Finset (Finset ℤ)}
    {T : Finset ℤ} (hlegal : Legal (Ground N) F) (htwo : 2≤F.card) (hT : T∈F) :
    T.Nonempty := by
  by_contra hn
  have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hall : ∀ S∈F,S=T := by
    intro S hS
    by_contra hST
    obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 S hS T hT hST)
    have hxT := (Finset.mem_inter.mp hx).2
    rw [he] at hxT
    exact Finset.notMem_empty x hxT
  have hc : F.card≤1 := Finset.card_le_one.mpr (by
    intro S hS U hU
    exact (hall S hS).trans (hall U hU).symm)
  omega

theorem actual_cover_by_member {N : ℕ} {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hT : T∈F) (hne : T.Nonempty) :
    F⊆T.biUnion (fun x => RootPart F x) := by
  intro S hS
  have hST : (S∩T).Nonempty := by
    by_cases he : S=T
    · simpa only [he,Finset.inter_self] using hne
    · exact isAP_nonempty (hlegal.2 S hS T hT he)
  obtain ⟨x,hx⟩ := hST
  obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_biUnion.mpr ⟨x,hxT,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩

theorem actual_direct_from_small_omitters {N L : ℕ}
    {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hT : T∈F) (hne : T.Nonempty)
    (homit : ∀ x∈T,∃ U∈F,x∉U ∧ U.card≤L) :
    F.card≤T.card*L*N := by
  have hc : ∀ x∈T,(RootPart F x).card≤L*N := by
    intro x hx
    obtain ⟨U,hUF,hxU,hUL⟩ := homit x hx
    exact (actual_omitter_root_linear hlegal hbad hUF hxU).trans
      (Nat.mul_le_mul_right N hUL)
  calc
    F.card≤(T.biUnion (fun x => RootPart F x)).card :=
      Finset.card_le_card (actual_cover_by_member hlegal hT hne)
    _≤∑x∈T,(RootPart F x).card := Finset.card_biUnion_le
    _≤∑_x∈T,L*N := Finset.sum_le_sum hc
    _=T.card*L*N := by simp [mul_assoc]

theorem actual_small_empty_kernel_direct {N L : ℕ}
    {F : Finset (Finset ℤ)} {T : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hT : T∈F) (hne : T.Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L)=∅) :
    F.card≤T.card*L*N := by
  apply actual_direct_from_small_omitters hlegal hbad hT hne
  intro x hx
  obtain ⟨U,hUS,hxU⟩ := actual_omitter_of_empty_kernel hkernel x (hlegal.1 T hT hx)
  obtain ⟨hUF,hUL⟩ := Finset.mem_filter.mp hUS
  exact ⟨U,hUF,hxU,hUL⟩

theorem actual_minimum_member_with_direct {N L : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S) (htwo : 2≤F.card)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L)=∅) :
    ∃ T∈F,0<T.card ∧ (∀ S∈F,T.card≤S.card) ∧ F.card≤T.card*L*N := by
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image F Finset.card hF
  have hne := actual_member_nonempty_of_two hlegal htwo hT
  exact ⟨T,hT,Finset.card_pos.mpr hne,hmin,
    actual_small_empty_kernel_direct hlegal hbad hT hne hkernel⟩

#print axioms actual_member_nonempty_of_two
#print axioms actual_cover_by_member
#print axioms actual_direct_from_small_omitters
#print axioms actual_small_empty_kernel_direct
#print axioms actual_minimum_member_with_direct
end
end JSP233.SmallKernel112
