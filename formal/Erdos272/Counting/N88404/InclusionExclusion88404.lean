module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Basic.Real.Basic
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.InclusionExclusion88404
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Intersect {α ι : Type*} (R : Finset α) (P : ι→α→Prop) (K : Finset ι) : Finset α :=
  R.filter fun x => ∀j∈K, P j x

def Avoid {α ι : Type*} (R : Finset α) (P : ι→α→Prop) (J : Finset ι) : Finset α :=
  R.filter fun x => ∀j∈J, ¬P j x

theorem intersect_empty {α ι : Type*} (R : Finset α) (P : ι→α→Prop) :
    Intersect R P ∅=R := by simp [Intersect]

theorem card_avoid_formula {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : Finset α) (P : ι→α→Prop) (J : Finset ι) :
    ((Avoid R P J).card : ℝ)=
      ∑K∈J.powerset, (-1 : ℝ)^K.card*((Intersect R P K).card : ℝ) := by
  let S : ι→Finset ↥R := fun j => Finset.univ.filter fun x => P j x.val
  have hcard (K : Finset ι) : (K.inf S).card=(Intersect R P K).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      have hp : ∀j∈K, P j x.val := by simpa [S, Finset.mem_inf] using hx
      exact Finset.mem_filter.mpr ⟨x.property, hp⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      have hp := (Finset.mem_filter.mp hx).2
      refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
      simpa [S, Finset.mem_inf] using hp
  have havoid : (J.inf (fun j => (S j)ᶜ)).card=(Avoid R P J).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      have hp : ∀j∈J, ¬P j x.val := by simpa [S, Finset.mem_inf] using hx
      exact Finset.mem_filter.mpr ⟨x.property, hp⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      have hp := (Finset.mem_filter.mp hx).2
      refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
      simpa [S, Finset.mem_inf] using hp
  have hz : ((Avoid R P J).card : ℤ)=
      ∑K∈J.powerset, (-1 : ℤ)^K.card*((Intersect R P K).card : ℤ) := by
    calc
      _ = ((J.inf (fun j => (S j)ᶜ)).card : ℤ) := by rw [havoid]
      _ = _ := Finset.inclusion_exclusion_card_inf_compl J S
      _ = _ := Finset.sum_congr rfl (fun K _ => by rw [hcard K])
  exact_mod_cast hz

theorem signed_product_sum {ι : Type*} (J : Finset ι) (v : ι→ℝ) :
    (∑K∈J.powerset, (-1 : ℝ)^K.card*∏j∈K, v j)=∏j∈J, (1-v j) := by
  simpa only [sub_eq_add_neg, Finset.prod_neg] using
    (Finset.prod_one_add (f := fun j => -v j) J).symm

#print axioms intersect_empty
#print axioms card_avoid_formula
#print axioms signed_product_sum
end
end JSP233.InclusionExclusion88404
