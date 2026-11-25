module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block024

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows025 : List Row := greedyEndpointRows 43681 11261895593981 47273

theorem checked025 : CheckRows 1000000000000 43681 11261895593981 rows025 = true := by
  decide +kernel

theorem end025 : RowsEnd 43681 11261895593981 rows025 = (47273, 11340920805482) := by
  decide +kernel

theorem sound025 (hp : 11261895593981 = FastDivSum 1000000000000 43681) :
    (∀ U : ℕ, 43681 ≤ U → U < 47273 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11340920805482 = FastDivSum 1000000000000 47273 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 43681) (h := 11261895593981)
    (rows := rows025) (by decide +kernel) hp checked025
  rw [end025] at hs
  exact hs

theorem prefix025 : 11261895593981 = FastDivSum 1000000000000 43681 :=
  (sound024 prefix024).2

theorem bound025 : ∀ U : ℕ, 2 ≤ U → U < 47273 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 43681
  · exact bound024 U hU hprev
  · exact (sound025 prefix025).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
