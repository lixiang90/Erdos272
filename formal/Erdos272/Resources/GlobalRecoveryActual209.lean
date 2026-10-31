import Erdos272.Resources.GlobalPreparation209
import Erdos272.Arithmetic.TotientExtended209

namespace JSP233.GlobalRecoveryActual209
open StarCompletion APGeometry DenseDeletion40
noncomputable section
set_option maxHeartbeats 0

theorem actual_inputs : FiniteRecovery209.TotientInputs 1540096 := by
  constructor
  · intro t ht
    exact (TotientExtended209.bounds t ht).1
  · intro t ht
    exact (TotientExtended209.bounds t ht).2

theorem actual_original_upper_of_root11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2000000 ≤ N) (hhigh : N ≤ 62443451) (hF : Legal (Ground N) F)
    (hcommon : ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S) : F.card ≤ B N := by
  exact GlobalPreparation209.actual_original_upper_of_root11 hN hhigh hF hcommon actual_inputs

#print axioms actual_inputs
#print axioms actual_original_upper_of_root11
end
end JSP233.GlobalRecoveryActual209
