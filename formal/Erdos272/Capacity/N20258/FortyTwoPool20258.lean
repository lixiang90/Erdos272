module

public import Erdos272.Resources.N158375.DensePool158375

@[expose] public section
namespace JSP233.FortyTwoPool20258
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Three small core lengths suffice to join the exact sieve to the
quadratic floor. No table of all possible cardinalities is required. -/
private theorem core_at_41 {a : ℕ} (lo : 41 ≤ a) (hi : a ≤ 2^18) : 446 ≤ UnitBound a := by
  by_cases large : 44 ≤ a
  · exact AnalyticCore180000.floor_split large hi (by decide) (by decide) (by decide)
  interval_cases a <;> decide +kernel

theorem member {N : ℕ} {S : Finset ℤ} (hi : N ≤ 2^18) (inGround : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 42 ≤ S.card) : 446 ≤ (Pool S).card := by
  have two : 2 ≤ S.card := by omega
  have size : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card inGround
  have core := (maxAPSize_le_card S).trans (size.trans hi)
  have split : MaxAPSize S+Defect S=S.card := by
    have := maxAPSize_le_card S
    unfold Defect
    omega
  have one := MixedCore200000.crooked_defect_positive two bad
  have prod := actual_union_core_source two
  by_cases many : 21 ≤ Defect S
  · exact (by decide : 446 ≤ 21*(21+1)).trans
      ((DensePool158375.physical_quadratic (s := S.card) (e := 21) (by omega)).trans
        (actual_source_of_defect two many))
  by_cases single : Defect S=1
  · rw [single,one_mul] at prod
    exact (core_at_41 (by omega) core).trans prod
  by_cases few : Defect S ≤ 4
  · have floor := AnalyticCore180000.floor_split (show 38 ≤ MaxAPSize S by omega) core
      (by decide) (by decide : 100*223+150*38 ≤ 27*38*38) (by decide)
    exact (by decide : 446 ≤ 2*223).trans ((Nat.mul_le_mul (by omega : 2 ≤ Defect S) floor).trans prod)
  have floor := AnalyticCore180000.floor_split (show 22 ≤ MaxAPSize S by omega) core
    (by decide) (by decide : 100*90+150*22 ≤ 27*22*22) (by decide)
  exact (by decide : 446 ≤ 5*90).trans ((Nat.mul_le_mul (by omega : 5 ≤ Defect S) floor).trans prod)

#print axioms member
end
end JSP233.FortyTwoPool20258
