module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block006

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows007 : List Row := greedyEndpointRows 6147 9301016437186 7255

theorem checked007 : CheckRows 1000000000000 6147 9301016437186 rows007 = true := by
  decide +kernel

theorem end007 : RowsEnd 6147 9301016437186 rows007 = (7255, 9466730743166) := by
  decide +kernel

theorem sound007 (hp : 9301016437186 = FastDivSum 1000000000000 6147) :
    (∀ U : ℕ, 6147 ≤ U → U < 7255 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9466730743166 = FastDivSum 1000000000000 7255 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 6147) (h := 9301016437186)
    (rows := rows007) (by decide +kernel) hp checked007
  rw [end007] at hs
  exact hs

theorem prefix007 : 9301016437186 = FastDivSum 1000000000000 6147 :=
  (sound006 prefix006).2

theorem bound007 : ∀ U : ℕ, 2 ≤ U → U < 7255 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 6147
  · exact bound006 U hU hprev
  · exact (sound007 prefix007).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
