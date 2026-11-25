module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block002

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows003 : List Row := greedyEndpointRows 2383 8353540945796 3241

theorem checked003 : CheckRows 1000000000000 2383 8353540945796 rows003 = true := by
  decide +kernel

theorem end003 : RowsEnd 2383 8353540945796 rows003 = (3241, 8661007131990) := by
  decide +kernel

theorem sound003 (hp : 8353540945796 = FastDivSum 1000000000000 2383) :
    (∀ U : ℕ, 2383 ≤ U → U < 3241 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      8661007131990 = FastDivSum 1000000000000 3241 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 2383) (h := 8353540945796)
    (rows := rows003) (by decide +kernel) hp checked003
  rw [end003] at hs
  exact hs

theorem prefix003 : 8353540945796 = FastDivSum 1000000000000 2383 :=
  (sound002 prefix002).2

theorem bound003 : ∀ U : ℕ, 2 ≤ U → U < 3241 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 2383
  · exact bound002 U hU hprev
  · exact (sound003 prefix003).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
