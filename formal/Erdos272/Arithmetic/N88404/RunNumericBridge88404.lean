module

public import Erdos272.Arithmetic.N88404.RunNumeric88404
public import Erdos272.Resources.N109474.RunSourcePlan109474

@[expose] public section

namespace JSP233.RunNumericBridge88404
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def toPlan (q : RunNumeric88404.Plan) : RunSource109474.Plan :=
  ⟨q.lower, q.defect, q.target, q.upper, q.heads⟩

theorem phi_checked : (List.range 128).all
    (fun n => decide (RunNumeric88404.phi n = FastDecode208.phi n)) = true := by
  decide +kernel

theorem phi_eq {n : ℕ} (hn : n < 128) :
    RunNumeric88404.phi n = FastDecode208.phi n :=
  of_decide_eq_true (List.all_eq_true.mp phi_checked n (List.mem_range.mpr hn))

theorem point_eq {s e h : ℕ} (hcap : s-e ≤ 128) :
    RunNumeric88404.point s e h = RunSource109474.point s e h := by
  unfold RunNumeric88404.point RunSource109474.point
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq128 : q < 128 := (Finset.mem_Ico.mp hq).2.trans_le hcap
  rw [phi_eq hq128]
  rfl

theorem conditions_sound {q : RunNumeric88404.Plan}
    (hq : RunNumeric88404.Conditions q) :
    RunSource109474.Conditions (toPlan q) := by
  rcases hq with ⟨hcap, he, hl, hu, hlen, hpoints⟩
  refine ⟨he, hl, hu, hlen, ?_⟩
  intro i hi
  have hp := hpoints i hi
  rcases hp with hshort | ⟨hh, hha, hpay⟩
  · exact Or.inl hshort
  · refine Or.inr ⟨hh, hha, ?_⟩
    have hir : i < q.heads.length := Finset.mem_range.mp hi
    have hlimit : q.lower+i-q.defect ≤ 128 := by omega
    exact hpay.trans (le_of_eq (point_eq hlimit))

#print axioms phi_checked
#print axioms phi_eq
#print axioms point_eq
#print axioms conditions_sound
end JSP233.RunNumericBridge88404
