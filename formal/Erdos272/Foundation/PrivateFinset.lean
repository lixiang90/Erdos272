module

public import Erdos272.Foundation.StarCompletion
public import Erdos272.Foundation.PrivateUnion
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
Finite-set bridge for the actual same-step private-point theorem.
`StarBound` in the final extremal corollary is an explicit mathematical
premise: the Yang starred upper bound has not been formalized here.
-/

namespace JSP233.PrivateFinset

open StarCompletion

theorem isAP_iff_predicate (S : Finset Int) :
    IsAP S ↔ PrivateUnion.IsAP (fun x => x ∈ S) := by
  constructor
  · rintro ⟨d, p, hd, lo, hi, hrep, hp⟩
    exact ⟨d, p, ⟨hd, lo, hi, hrep⟩, hp⟩
  · rintro ⟨d, p, ⟨hd, lo, hi, hrep⟩, hp⟩
    exact ⟨d, p, hd, lo, hi, hrep, hp⟩

noncomputable def Kernel (Ω : Finset Int) (D : Finset (Finset Int)) : Finset Int :=
  Ω.filter (fun x => ∀ S ∈ D, x ∈ S)

/-- Genuine cardinality payment: the ground and kernel enumerate actual
integer points, not numeric resources supplied as assumptions. -/
theorem same_step_card_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (d p : Int) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hp : ∀ S ∈ D, p ∈ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt d p (fun x => x ∈ S ∧ x ∈ T)) :
    D.card + (Kernel Ω D).card ≤ Ω.card := by
  classical
  let e := D.equivFin.symm
  let A : Fin D.card → Int → Prop := fun i x => x ∈ (e i).val
  have hcrookedA : ∀ i, ¬ PrivateUnion.IsAP (A i) := by
    intro i hi
    exact hcrooked (e i).val (e i).property
      ((isAP_iff_predicate (e i).val).mpr hi)
  have hpA : ∀ i, A i p := fun i => hp _ (e i).property
  have hpairs : ∀ i j, i ≠ j → PrivateUnion.APAt d p (fun x => A i x ∧ A j x) := by
    intro i j hij
    apply hpair _ (e i).property _ (e j).property
    intro heq
    apply hij
    apply e.injective
    exact Subtype.ext heq
  have hres := PrivateUnion.family_add_kernel_le_ground_length d p A
    Ω.toList (Kernel Ω D).toList hm hcrookedA hpA hpairs
    (by intro i x hx; exact Finset.mem_toList.mpr (hground _ (e i).property hx))
    (by
      intro x hx i
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2 _ (e i).property)
    (Finset.nodup_toList _)
  simpa only [Finset.length_toList] using hres

theorem kernel_erase_root (Ω : Finset Int) (D : Finset (Finset Int))
    (c : Int) (hD : D.Nonempty) (havoid : ∀ S ∈ D, c ∉ S) :
    Kernel (Ω.erase c) D = Kernel Ω D := by
  classical
  ext x
  simp only [Kernel, Finset.mem_filter, Finset.mem_erase]
  constructor
  · intro hx
    exact ⟨hx.1.2, hx.2⟩
  · intro hx
    refine ⟨⟨?_, hx.1⟩, hx.2⟩
    intro heq
    rcases hD with ⟨S, hS⟩
    exact havoid S hS (heq ▸ hx.2 S hS)

/-- Avoiding an actual ground point saves one additional unit. -/
theorem same_step_avoiders_card_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (c d p : Int) (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hp : ∀ S ∈ D, p ∈ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt d p (fun x => x ∈ S ∧ x ∈ T)) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  classical
  have hgr : ∀ S ∈ D, S ⊆ Ω.erase c := by
    intro S hS x hx
    exact Finset.mem_erase.mpr ⟨by intro heq; exact havoid S hS (heq ▸ hx), hground S hS hx⟩
  have hD : D.Nonempty := Finset.card_pos.mp (by omega)
  have hbound := same_step_card_bound (Ω.erase c) D d p hm hgr hcrooked hp hpair
  rw [kernel_erase_root Ω D c hD havoid, Finset.card_erase_of_mem hc] at hbound
  have hΩ : 0 < Ω.card := Finset.card_pos.mpr ⟨c, hc⟩
  omega

/-- The same-step omitted family is connected to the original legal family.
The starred bound is the only unproved extremal input. -/
theorem same_step_avoiders_payment (Ω : Finset Int) (F : Finset (Finset Int))
    (c d p : Int) (B : Nat) (hc : c ∈ Ω) (hF : Legal Ω F)
    (hstar : StarBound Ω B) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hp : ∀ S ∈ Avoiders F c, p ∈ S)
    (hpair : ∀ S ∈ Avoiders F c, ∀ T ∈ Avoiders F c, S ≠ T →
      PrivateUnion.APAt d p (fun x => x ∈ S ∧ x ∈ T)) :
    F.card + 1 ≤ B := by
  classical
  have hground : ∀ S ∈ Avoiders F c, S ⊆ Ω := by
    intro S hS
    exact hF.1 S (Finset.mem_filter.mp hS).1
  have havoid : ∀ S ∈ Avoiders F c, c ∉ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hcap := same_step_avoiders_card_bound Ω (Avoiders F c) c d p hc hm
    hground havoid hcrooked hp hpair
  have hpay := completion_payment Ω F c B hc hF hstar
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  omega

#print axioms isAP_iff_predicate
#print axioms same_step_card_bound
#print axioms kernel_erase_root
#print axioms same_step_avoiders_card_bound
#print axioms same_step_avoiders_payment

end JSP233.PrivateFinset
