module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block007

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows008 : List Row := greedyEndpointRows 7255 9466730743166 8461

theorem checked008 : CheckRows 1000000000000 7255 9466730743166 rows008 = true := by
  decide +kernel

theorem end008 : RowsEnd 7255 9466730743166 rows008 = (8461, 9620497403306) := by
  decide +kernel

theorem sound008 (hp : 9466730743166 = FastDivSum 1000000000000 7255) :
    (∀ U : ℕ, 7255 ≤ U → U < 8461 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9620497403306 = FastDivSum 1000000000000 8461 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 7255) (h := 9466730743166)
    (rows := rows008) (by decide +kernel) hp checked008
  rw [end008] at hs
  exact hs

theorem prefix008 : 9466730743166 = FastDivSum 1000000000000 7255 :=
  (sound007 prefix007).2

theorem bound008 : ∀ U : ℕ, 2 ≤ U → U < 8461 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 7255
  · exact bound007 U hU hprev
  · exact (sound008 prefix008).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
