module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block036

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows037 : List Row := greedyEndpointRows 105451 12143222023461 112833

theorem checked037 : CheckRows 1000000000000 105451 12143222023461 rows037 = true := by
  decide +kernel

theorem end037 : RowsEnd 105451 12143222023461 rows037 = (112833, 12210884169037) := by
  decide +kernel

theorem sound037 (hp : 12143222023461 = FastDivSum 1000000000000 105451) :
    (∀ U : ℕ, 105451 ≤ U → U < 112833 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12210884169037 = FastDivSum 1000000000000 112833 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 105451) (h := 12143222023461)
    (rows := rows037) (by decide +kernel) hp checked037
  rw [end037] at hs
  exact hs

theorem prefix037 : 12143222023461 = FastDivSum 1000000000000 105451 :=
  (sound036 prefix036).2

theorem bound037 : ∀ U : ℕ, 2 ≤ U → U < 112833 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 105451
  · exact bound036 U hU hprev
  · exact (sound037 prefix037).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
