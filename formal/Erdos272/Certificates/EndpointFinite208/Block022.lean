module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block021

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows022 : List Row := greedyEndpointRows 34082 11013754983331 37096

theorem checked022 : CheckRows 1000000000000 34082 11013754983331 rows022 = true := by
  decide +kernel

theorem end022 : RowsEnd 34082 11013754983331 rows022 = (37096, 11098493551283) := by
  decide +kernel

theorem sound022 (hp : 11013754983331 = FastDivSum 1000000000000 34082) :
    (∀ U : ℕ, 34082 ≤ U → U < 37096 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11098493551283 = FastDivSum 1000000000000 37096 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 34082) (h := 11013754983331)
    (rows := rows022) (by decide +kernel) hp checked022
  rw [end022] at hs
  exact hs

theorem prefix022 : 11013754983331 = FastDivSum 1000000000000 34082 :=
  (sound021 prefix021).2

theorem bound022 : ∀ U : ℕ, 2 ≤ U → U < 37096 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 34082
  · exact bound021 U hU hprev
  · exact (sound022 prefix022).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
