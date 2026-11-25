module

public import Erdos272.Capacity.N20258.UniformCardPool20258
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Resources.N86412.StrictRunSource86412

@[expose] public section
namespace JSP233.TwoOutsidePool20258
open StarCompletion SourceBridge208 IntrinsicTriples208
set_option autoImplicit false

/-- For the short sizes the one run beginning halfway along the size range
already pays the full natural head, with both outside points counted. -/
private theorem finite : ∀ i : Fin 17,
    let s := 43+i.val
    (s-1).choose 2≤StrictRunNumeric86412.point s 2 ((s+1)/2) := by
  set_option maxRecDepth 16000 in decide +kernel

theorem short {S : Finset ℤ} (lo : 43≤S.card) (hi : S.card≤59)
    (two : 2≤Defect S) : (S.card-1).choose 2≤(Pool S).card := by
  let i : Fin 17 := ⟨S.card-43,by omega⟩
  have eqn : 43+i.val=S.card := by dsimp [i]; omega
  have price := finite i
  dsimp only at price
  rw [eqn,StrictRunNumericBridge86412.point_eq (by omega)] at price
  exact price.trans (StrictRunSource86412.actual_point_source (by omega) (by omega)
    (by decide : 2≤2) two (by omega) (by omega))

/-- A bound on the original member, valid even when its size is above
the entire finite run table. -/
theorem member {S : Finset ℤ} {N C : ℕ} (ground : S⊆Ground N) (cap : N≤2^18)
    (lo : 43≤C) (hi : C≤45) (size : C≤S.card) (two : 2≤Defect S) :
    (C-1).choose 2≤(Pool S).card := by
  by_cases small : S.card≤59
  · exact (Nat.choose_le_choose 2 (Nat.sub_le_sub_right size 1)).trans
      (short (lo.trans size) small two)
  · have neq := StrictAP86412.notAP_of_defect (by decide : 1≤2) two
    exact (Nat.choose_le_choose 2 (show C-1≤44 by omega)).trans
      (UniformCardPool20258.pool_floor (s:=60) cap ground neq (by decide) (by decide)
        (by omega) (by decide +kernel))

#print axioms short
#print axioms member
end JSP233.TwoOutsidePool20258
