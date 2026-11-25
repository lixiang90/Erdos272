module

public import Erdos272.Arithmetic.N88404.RunNumericBridge88404
public import Erdos272.Arithmetic.N86412.StrictRunNumeric86412
public import Erdos272.Resources.N86412.StrictRunSourcePlan86412

@[expose] public section

namespace JSP233.StrictRunNumericBridge86412
set_option autoImplicit false
set_option maxHeartbeats 0

theorem point_eq {s e h : ℕ} (hcap : s-e ≤ 128) :
    StrictRunNumeric86412.point s e h = StrictRunSource86412.point s e h := by
  unfold StrictRunNumeric86412.point StrictRunSource86412.point
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq128 : q < 128 := (Finset.mem_Ico.mp hq).2.trans_le hcap
  rw [RunNumericBridge88404.phi_eq hq128]
  rfl

theorem conditions_sound {q : RunNumeric88404.Plan}
    (hq : StrictRunNumeric86412.Conditions q) :
    StrictRunSource86412.Conditions (RunNumericBridge88404.toPlan q) := by
  rcases hq with ⟨hcap, he₂, he, hl, hu, hlen, hpoints⟩
  refine ⟨he₂, he, hl, hu, hlen, ?_⟩
  intro i hi
  rcases hpoints i hi with hshort | ⟨hh, hha, hpay⟩
  · exact Or.inl hshort
  · refine Or.inr ⟨hh, hha, ?_⟩
    have hir : i < q.heads.length := Finset.mem_range.mp hi
    have hlimit : q.lower+i-q.defect ≤ 128 := by omega
    exact hpay.trans (le_of_eq (point_eq hlimit))

#print axioms point_eq
#print axioms conditions_sound
end JSP233.StrictRunNumericBridge86412
