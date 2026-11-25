module

public import Erdos272.Counting.N86412.StrictAP86412
public import Erdos272.Counting.N86412.UniformStrictBridge86412

@[expose] public section

namespace JSP233.StrictPool86412
open StarCompletion SourceBridge208 IntrinsicTriples208 ActualAPCount208 PureSource208
open APInterval208 StrictAP86412 UniformStrictBridge86412 TotientStrict86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_U_le_pool (S : Finset ℤ) (hS : 4≤S.card) (hnot : ¬IsAP S) :
    U S.card≤(Pool S).card := by
  apply actual_uniform_of_counts hS
  intro q hq
  unfold Credit
  split_ifs with hc
  · exact actual_strict_count hc.1 (Finset.mem_Ico.mp hq).2 hnot (Or.inr hc.2)
  · simpa only [Nat.add_zero] using
      actual_AP_count_le_interval (by have hh := (Finset.mem_Ico.mp hq).1; omega) S

theorem actual_U_of_defect {S : Finset ℤ} {e : ℕ} (hS : 4≤S.card)
    (he : 1≤e) (heD : e≤Defect S) : U S.card≤(Pool S).card :=
  actual_U_le_pool S hS (notAP_of_defect he heD)

#print axioms actual_U_le_pool
#print axioms actual_U_of_defect
end
end JSP233.StrictPool86412
