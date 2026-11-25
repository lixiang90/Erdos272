module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block005

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows006 : List Row := greedyEndpointRows 5111 9116463846291 6147

theorem checked006 : CheckRows 1000000000000 5111 9116463846291 rows006 = true := by
  decide +kernel

theorem end006 : RowsEnd 5111 9116463846291 rows006 = (6147, 9301016437186) := by
  decide +kernel

theorem sound006 (hp : 9116463846291 = FastDivSum 1000000000000 5111) :
    (∀ U : ℕ, 5111 ≤ U → U < 6147 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9301016437186 = FastDivSum 1000000000000 6147 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 5111) (h := 9116463846291)
    (rows := rows006) (by decide +kernel) hp checked006
  rw [end006] at hs
  exact hs

theorem prefix006 : 9116463846291 = FastDivSum 1000000000000 5111 :=
  (sound005 prefix005).2

theorem bound006 : ∀ U : ℕ, 2 ≤ U → U < 6147 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 5111
  · exact bound005 U hU hprev
  · exact (sound006 prefix006).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
