import Erdos272.Arithmetic.BatchSourceBlocks208
import Erdos272.Arithmetic.SourceTargets208

/-! Only the 2405 adjacent scalar target comparisons are evaluated here.
No totient lookup or physical-source rectangle is computed. -/
namespace JSP233.SourceTargetOrder208
open BatchSourceBlocks208 SourceTargets208
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem targets_length : Targets.length = 14 := by decide +kernel

theorem targets_adjacent : adjacentCheck Targets = true := by decide +kernel

theorem target_row_length {row : ℕ × List ℕ} (hrow : row ∈ Targets) : row.2.length = 185 := by
  have hc : Targets.all (fun r => decide (r.2.length = 185)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp hc) row hrow)

def targetAt (i : Fin 14) : ℕ × List ℕ :=
  Targets[i.val]'(by rw [targets_length]; exact i.isLt)

theorem targetAt_length (i : Fin 14) : (targetAt i).2.length = 185 := by
  exact target_row_length (List.getElem_mem (by rw [targets_length]; exact i.isLt))

theorem adjacent_targets {i : ℕ} (hi : i + 1 < 14) :
    (targetAt ⟨i, by omega⟩).1 ≤ (targetAt ⟨i + 1, hi⟩).1 ∧
      rowLE (targetAt ⟨i, by omega⟩).2 (targetAt ⟨i + 1, hi⟩).2 = true := by
  exact adjacentCheck_get targets_adjacent i (by simpa only [targets_length] using hi)

theorem adjacent_target_floor {i e : ℕ} (hi : i + 1 < 14) (he : e < 185) :
    (targetAt ⟨i, by omega⟩).2[e]'(by rw [targetAt_length]; exact he) ≤
      (targetAt ⟨i + 1, hi⟩).2[e]'(by rw [targetAt_length]; exact he) := by
  exact rowLE_get (adjacent_targets hi).2 e (by rw [targetAt_length]; exact he)
    (by rw [targetAt_length]; exact he)

#print axioms targets_adjacent
#print axioms adjacent_targets
#print axioms adjacent_target_floor
end JSP233.SourceTargetOrder208
