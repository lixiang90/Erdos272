module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block028

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows029 : List Row := greedyEndpointRows 59536 11571560484479 64169

theorem checked029 : CheckRows 1000000000000 59536 11571560484479 rows029 = true := by
  decide +kernel

theorem end029 : RowsEnd 59536 11571560484479 rows029 = (64169, 11646498932268) := by
  decide +kernel

theorem sound029 (hp : 11571560484479 = FastDivSum 1000000000000 59536) :
    (∀ U : ℕ, 59536 ≤ U → U < 64169 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11646498932268 = FastDivSum 1000000000000 64169 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 59536) (h := 11571560484479)
    (rows := rows029) (by decide +kernel) hp checked029
  rw [end029] at hs
  exact hs

theorem prefix029 : 11571560484479 = FastDivSum 1000000000000 59536 :=
  (sound028 prefix028).2

theorem bound029 : ∀ U : ℕ, 2 ≤ U → U < 64169 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 59536
  · exact bound028 U hU hprev
  · exact (sound029 prefix029).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
