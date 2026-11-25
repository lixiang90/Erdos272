module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block012

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows013 : List Row := greedyEndpointRows 14145 10134367489550 15823

theorem checked013 : CheckRows 1000000000000 14145 10134367489550 rows013 = true := by
  decide +kernel

theorem end013 : RowsEnd 14145 10134367489550 rows013 = (15823, 10246467113178) := by
  decide +kernel

theorem sound013 (hp : 10134367489550 = FastDivSum 1000000000000 14145) :
    (∀ U : ℕ, 14145 ≤ U → U < 15823 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10246467113178 = FastDivSum 1000000000000 15823 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 14145) (h := 10134367489550)
    (rows := rows013) (by decide +kernel) hp checked013
  rw [end013] at hs
  exact hs

theorem prefix013 : 10134367489550 = FastDivSum 1000000000000 14145 :=
  (sound012 prefix012).2

theorem bound013 : ∀ U : ℕ, 2 ≤ U → U < 15823 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 14145
  · exact bound012 U hU hprev
  · exact (sound013 prefix013).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
