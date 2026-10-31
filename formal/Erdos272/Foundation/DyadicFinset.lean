import Erdos272.Foundation.PrivateFinset
import Erdos272.Foundation.DyadicStencil

/-!
Actual finite integer-set dyadic-stencil payment.  The eight displayed APs
are actual family members.  Their traces force the pairwise step, which
then gives a genuine cardinality payment.  Only `StarBound` remains an
explicit external extremal premise; same-step intersections are not assumed.
-/

namespace JSP233.DyadicFinset

open StarCompletion

def stencilSet (c d : Int) (s : Fin 8) : Finset Int :=
  (EightAPStencil.stencil s).toFinset.image (EightAPStencil.affine c d)

def PredicateFamily (F : Finset (Finset Int)) (A : Int → Prop) : Prop :=
  ∃ S ∈ F, A = (fun x => x ∈ S)

theorem isAP_iff_eightAPStencil (S : Finset Int) :
    IsAP S ↔ EightAPStencil.IsAP (fun x => x ∈ S) := by
  exact (PrivateFinset.isAP_iff_predicate S).trans
    (DyadicStencil.isAP_iff_privateUnion (fun x => x ∈ S)).symm

theorem mem_stencilSet (c d : Int) (s : Fin 8) (x : Int) :
    x ∈ stencilSet c d s ↔
      EightAPStencil.onGrid c d (EightAPStencil.stencil s) x := by
  simp only [stencilSet, Finset.mem_image, List.mem_toFinset, EightAPStencil.onGrid]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hx.symm⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hx.symm⟩

theorem legal_predicateFamily (Ω : Finset Int) (F : Finset (Finset Int))
    (hF : Legal Ω F) : EightAPStencil.Legal (PredicateFamily F) := by
  intro A B hA hB hne
  obtain ⟨S, hS, rfl⟩ := hA
  obtain ⟨T, hT, rfl⟩ := hB
  have hST : S ≠ T := by
    intro he
    subst T
    exact hne rfl
  have hp := (isAP_iff_eightAPStencil (S ∩ T)).mp (hF.2 S hS T hT hST)
  simpa only [Finset.mem_inter] using hp

theorem actual_stencils_predicateFamily
    (F : Finset (Finset Int)) (c d : Int)
    (hstencils : ∀ s : Fin 8, stencilSet c d s ∈ F) :
    ∀ s : Fin 8,
      PredicateFamily F (EightAPStencil.onGrid c d (EightAPStencil.stencil s)) := by
  intro s
  refine ⟨stencilSet c d s, hstencils s, ?_⟩
  funext x
  exact propext (mem_stencilSet c d s x).symm

theorem actual_stencil_root_in_ambient
    (Ω : Finset Int) (F : Finset (Finset Int)) (c d : Int)
    (hF : Legal Ω F) (hstencils : ∀ s : Fin 8, stencilSet c d s ∈ F) :
    c ∈ Ω := by
  apply hF.1 _ (hstencils 0)
  exact (mem_stencilSet c d 0 c).mpr (EightAPStencil.stencil_contains_root c d 0)

theorem actual_avoider_contains_bridge
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (j : Nat)
    (hF : Legal Ω F)
    (hstencils : ∀ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∈ F)
    (S : Finset Int) (hS : S ∈ Avoiders F c) :
    c - 2 * DyadicStencil.step j ∈ S ∧ c + 2 * DyadicStencil.step j ∈ S := by
  apply DyadicStencil.actual_stencil_bridge (PredicateFamily F)
    (legal_predicateFamily Ω F hF) (fun x => x ∈ S)
    ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩ c j
    (Finset.mem_filter.mp hS).2
    (actual_stencils_predicateFamily F c (DyadicStencil.step j) hstencils)

theorem actual_avoider_intersection_step
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (j : Nat)
    (hF : Legal Ω F)
    (hstencils : ∀ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∈ F)
    (S : Finset Int) (hS : S ∈ Avoiders F c)
    (T : Finset Int) (hT : T ∈ Avoiders F c) (hne : S ≠ T) :
    PrivateUnion.APAt (4 * DyadicStencil.step j) (c - 2 * DyadicStencil.step j)
      (fun x => x ∈ S ∧ x ∈ T) := by
  have hSb := actual_avoider_contains_bridge Ω F c j hF hstencils S hS
  have hTb := actual_avoider_contains_bridge Ω F c j hF hstencils T hT
  have hAP := (isAP_iff_eightAPStencil (S ∩ T)).mp
    (hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne)
  apply DyadicStencil.bridge_forces_step (fun x => x ∈ S ∧ x ∈ T) c j
    (by simpa only [Finset.mem_inter] using hAP)
  · exact ⟨hSb.1,hTb.1⟩
  · exact ⟨hSb.2,hTb.2⟩
  · intro hroot
    exact (Finset.mem_filter.mp hS).2 hroot.1

/-- Actual dyadic eight-member entry: the entire original finite family
lies strictly below B whenever there are at least two crooked omitters.
The common step is derived from the actual AP intersections above. -/
theorem actual_dyadic_stencil_strict_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (j B : Nat)
    (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hstencils : ∀ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∈ F) :
    F.card + 1 ≤ B := by
  have hc := actual_stencil_root_in_ambient Ω F c (DyadicStencil.step j) hF hstencils
  apply PrivateFinset.same_step_avoiders_payment Ω F
    c (4 * DyadicStencil.step j) (c - 2 * DyadicStencil.step j) B hc hF hstar hm hcrooked
  · intro S hS
    exact (actual_avoider_contains_bridge Ω F c j hF hstencils S hS).1
  · intro S hS T hT hne
    exact actual_avoider_intersection_step Ω F c j hF hstencils S hS T hT hne

/-- This version includes zero or one omitter, where the strict saving is
not asserted. The actual stencil members themselves certify c∈Ω. -/
theorem actual_dyadic_stencil_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (j B : Nat)
    (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hstencils : ∀ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∈ F) :
    F.card ≤ B := by
  by_cases hm : 2 ≤ (Avoiders F c).card
  · have hs := actual_dyadic_stencil_strict_payment Ω F c j B hF hstar hm hcrooked hstencils
    omega
  · apply at_most_one_avoider_payment Ω F c B
      (actual_stencil_root_in_ambient Ω F c (DyadicStencil.step j) hF hstencils) hF hstar
    omega

/-- A surviving counterexample must omit at least one of the eight actual
APs at every dyadic scale.  No root-membership premise is added: a complete
stencil would itself certify that premise inside the payment theorem. -/
theorem counterexample_omits_each_dyadic_stencil
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (B : Nat)
    (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) (hover : B < F.card) :
    ∀ j : Nat, ∃ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∉ F := by
  classical
  intro j
  by_contra hnone
  have hall : ∀ s : Fin 8, stencilSet c (DyadicStencil.step j) s ∈ F := by
    intro s
    by_contra hs
    exact hnone ⟨s,hs⟩
  have hpay := actual_dyadic_stencil_payment Ω F c j B hF hstar hcrooked hall
  omega

#print axioms isAP_iff_eightAPStencil
#print axioms mem_stencilSet
#print axioms legal_predicateFamily
#print axioms actual_stencils_predicateFamily
#print axioms actual_stencil_root_in_ambient
#print axioms actual_avoider_contains_bridge
#print axioms actual_avoider_intersection_step
#print axioms actual_dyadic_stencil_strict_payment
#print axioms actual_dyadic_stencil_payment
#print axioms counterexample_omits_each_dyadic_stencil

end JSP233.DyadicFinset
