module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block025

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows026 : List Row := greedyEndpointRows 47273 11340920805482 51101

theorem checked026 : CheckRows 1000000000000 47273 11340920805482 rows026 = true := by
  decide +kernel

theorem end026 : RowsEnd 47273 11340920805482 rows026 = (51101, 11418784769776) := by
  decide +kernel

theorem sound026 (hp : 11340920805482 = FastDivSum 1000000000000 47273) :
    (∀ U : ℕ, 47273 ≤ U → U < 51101 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11418784769776 = FastDivSum 1000000000000 51101 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 47273) (h := 11340920805482)
    (rows := rows026) (by decide +kernel) hp checked026
  rw [end026] at hs
  exact hs

theorem prefix026 : 11340920805482 = FastDivSum 1000000000000 47273 :=
  (sound025 prefix025).2

theorem bound026 : ∀ U : ℕ, 2 ≤ U → U < 51101 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 47273
  · exact bound025 U hU hprev
  · exact (sound026 prefix026).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
