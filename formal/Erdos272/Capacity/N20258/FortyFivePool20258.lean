module

public import Erdos272.Capacity.N20258.FortyTwoPool20258

@[expose] public section
namespace JSP233.FortyFivePool20258
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 CoreUnionSource200000
open PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem core {a : ℕ} (lo : 44 ≤ a) (hi : a ≤ 2^18) : 529 ≤ UnitBound a := by
  by_cases large : 48 ≤ a
  · exact AnalyticCore180000.floor_split large hi (by decide) (by decide) (by decide)
  interval_cases a <;> decide +kernel

/-- A crooked member on at least 45 sites pays 529 private triples. -/
theorem member {N : ℕ} {S : Finset ℤ} (hi : N ≤ 2^18) (inside : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 45 ≤ S.card) : 529 ≤ (Pool S).card := by
  have two : 2 ≤ S.card := by omega
  have size : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card inside
  have top := (maxAPSize_le_card S).trans (size.trans hi)
  have split : MaxAPSize S+Defect S=S.card := by
    have := maxAPSize_le_card S
    unfold Defect
    omega
  have one := MixedCore200000.crooked_defect_positive two bad
  have prod := actual_union_core_source two
  by_cases many : 23 ≤ Defect S
  · exact (by decide : 529 ≤ 23*(23+1)).trans
      ((DensePool158375.physical_quadratic (s := S.card) (e := 23) (by omega)).trans
        (actual_source_of_defect two many))
  by_cases single : Defect S=1
  · rw [single,one_mul] at prod
    exact (core (by omega) top).trans prod
  by_cases few : Defect S ≤ 4
  · have floor := AnalyticCore180000.floor_split (show 41 ≤ MaxAPSize S by omega) top
      (by decide) (by decide : 100*265+150*41 ≤ 27*41*41) (by decide)
    exact (by decide : 529 ≤ 2*265).trans ((Nat.mul_le_mul (by omega : 2 ≤ Defect S) floor).trans prod)
  have floor := AnalyticCore180000.floor_split (show 23 ≤ MaxAPSize S by omega) top
    (by decide) (by decide : 100*106+150*23 ≤ 27*23*23) (by decide)
  exact (by decide : 529 ≤ 5*106).trans ((Nat.mul_le_mul (by omega : 5 ≤ Defect S) floor).trans prod)

/-- Only the members of the 44-site layer receive the 83-triple rebate. -/
theorem family {N : ℕ} {F : Finset (Finset ℤ)} (hi : N ≤ 2^18) (legal : Legal (Ground N) F)
    (large : ∀ S ∈ F, 44 ≤ S.card)
    (layer : ((CrookedMembers F).filter (fun S => S.card=44)).card ≤ 44*N) :
    529*((CrookedMembers F).card : ℝ) ≤
      (∑ S ∈ F, ((Pool S).card : ℝ))+83*44*N := by
  let H := CrookedMembers F
  have sub : H ⊆ F := Finset.filter_subset _ _
  have each (S : Finset ℤ) (hs : S ∈ H) :
      (529 : ℝ) ≤ ((Pool S).card : ℝ)+(if S.card=44 then 83 else 0) := by
    have bad := (Finset.mem_filter.mp hs).2
    have sz := large S (sub hs)
    by_cases eqn : S.card=44
    · rw [if_pos eqn]
      have h : 446 ≤ (Pool S).card := FortyTwoPool20258.member hi (legal.1 S (sub hs)) bad (by omega)
      exact_mod_cast (show 529 ≤ (Pool S).card+83 by omega)
    · rw [if_neg eqn,add_zero]
      exact_mod_cast member hi (legal.1 S (sub hs)) bad (by omega)
  have paid := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,←Finset.sum_filter] at paid
  simp only [Finset.sum_const,nsmul_eq_mul] at paid
  have mass := Finset.sum_le_sum_of_subset_of_nonneg (f := fun S : Finset ℤ => ((Pool S).card : ℝ))
    sub (fun _ _ _ => by positivity)
  have cheap : (((H.filter (fun S => S.card=44)).card : ℕ) : ℝ) ≤ 44*N := by exact_mod_cast layer
  linarith only [paid,mass,cheap]

#print axioms family
end
end JSP233.FortyFivePool20258
