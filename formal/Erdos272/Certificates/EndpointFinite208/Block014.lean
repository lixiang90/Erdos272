module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block013

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows014 : List Row := greedyEndpointRows 15823 10246467113178 17623

theorem checked014 : CheckRows 1000000000000 15823 10246467113178 rows014 = true := by
  decide +kernel

theorem end014 : RowsEnd 15823 10246467113178 rows014 = (17623, 10354204174156) := by
  decide +kernel

theorem sound014 (hp : 10246467113178 = FastDivSum 1000000000000 15823) :
    (∀ U : ℕ, 15823 ≤ U → U < 17623 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10354204174156 = FastDivSum 1000000000000 17623 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 15823) (h := 10246467113178)
    (rows := rows014) (by decide +kernel) hp checked014
  rw [end014] at hs
  exact hs

theorem prefix014 : 10246467113178 = FastDivSum 1000000000000 15823 :=
  (sound013 prefix013).2

theorem bound014 : ∀ U : ℕ, 2 ≤ U → U < 17623 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 15823
  · exact bound013 U hU hprev
  · exact (sound014 prefix014).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
