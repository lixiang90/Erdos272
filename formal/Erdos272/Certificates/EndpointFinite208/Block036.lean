module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block035

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows036 : List Row := greedyEndpointRows 98463 12074656816489 105451

theorem checked036 : CheckRows 1000000000000 98463 12074656816489 rows036 = true := by
  decide +kernel

theorem end036 : RowsEnd 98463 12074656816489 rows036 = (105451, 12143222023461) := by
  decide +kernel

theorem sound036 (hp : 12074656816489 = FastDivSum 1000000000000 98463) :
    (∀ U : ℕ, 98463 ≤ U → U < 105451 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12143222023461 = FastDivSum 1000000000000 105451 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 98463) (h := 12074656816489)
    (rows := rows036) (by decide +kernel) hp checked036
  rw [end036] at hs
  exact hs

theorem prefix036 : 12074656816489 = FastDivSum 1000000000000 98463 :=
  (sound035 prefix035).2

theorem bound036 : ∀ U : ℕ, 2 ≤ U → U < 105451 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 98463
  · exact bound035 U hU hprev
  · exact (sound036 prefix036).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
