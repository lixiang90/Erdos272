module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block011

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows012 : List Row := greedyEndpointRows 12583 10017357370059 14145

theorem checked012 : CheckRows 1000000000000 12583 10017357370059 rows012 = true := by
  decide +kernel

theorem end012 : RowsEnd 12583 10017357370059 rows012 = (14145, 10134367489550) := by
  decide +kernel

theorem sound012 (hp : 10017357370059 = FastDivSum 1000000000000 12583) :
    (∀ U : ℕ, 12583 ≤ U → U < 14145 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10134367489550 = FastDivSum 1000000000000 14145 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 12583) (h := 10017357370059)
    (rows := rows012) (by decide +kernel) hp checked012
  rw [end012] at hs
  exact hs

theorem prefix012 : 10017357370059 = FastDivSum 1000000000000 12583 :=
  (sound011 prefix011).2

theorem bound012 : ∀ U : ℕ, 2 ≤ U → U < 14145 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 12583
  · exact bound011 U hU hprev
  · exact (sound012 prefix012).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
