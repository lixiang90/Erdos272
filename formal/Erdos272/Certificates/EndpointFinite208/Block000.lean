module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Counting.EndpointGate208

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows000 : List Row := greedyEndpointRows 2 1500000000000 814

theorem checked000 : CheckRows 1000000000000 2 1500000000000 rows000 = true := by
  decide +kernel

theorem end000 : RowsEnd 2 1500000000000 rows000 = (814, 7279790155404) := by
  decide +kernel

theorem sound000 (hp : 1500000000000 = FastDivSum 1000000000000 2) :
    (∀ U : ℕ, 2 ≤ U → U < 814 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      7279790155404 = FastDivSum 1000000000000 814 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 2) (h := 1500000000000)
    (rows := rows000) (by decide +kernel) hp checked000
  rw [end000] at hs
  exact hs

theorem prefix000 : 1500000000000 = FastDivSum 1000000000000 2 := by decide +kernel

theorem bound000 : ∀ U : ℕ, 2 ≤ U → U < 814 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U :=
  (sound000 prefix000).1

end
end JSP233.EndpointFinite208
