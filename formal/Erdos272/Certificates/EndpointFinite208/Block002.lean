module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block001

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows002 : List Row := greedyEndpointRows 1583 7944608546803 2383

theorem checked002 : CheckRows 1000000000000 1583 7944608546803 rows002 = true := by
  decide +kernel

theorem end002 : RowsEnd 1583 7944608546803 rows002 = (2383, 8353540945796) := by
  decide +kernel

theorem sound002 (hp : 7944608546803 = FastDivSum 1000000000000 1583) :
    (∀ U : ℕ, 1583 ≤ U → U < 2383 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      8353540945796 = FastDivSum 1000000000000 2383 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 1583) (h := 7944608546803)
    (rows := rows002) (by decide +kernel) hp checked002
  rw [end002] at hs
  exact hs

theorem prefix002 : 7944608546803 = FastDivSum 1000000000000 1583 :=
  (sound001 prefix001).2

theorem bound002 : ∀ U : ℕ, 2 ≤ U → U < 2383 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 1583
  · exact bound001 U hU hprev
  · exact (sound002 prefix002).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
