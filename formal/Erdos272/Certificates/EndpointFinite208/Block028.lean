module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block027

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows028 : List Row := greedyEndpointRows 55179 11495562424261 59536

theorem checked028 : CheckRows 1000000000000 55179 11495562424261 rows028 = true := by
  decide +kernel

theorem end028 : RowsEnd 55179 11495562424261 rows028 = (59536, 11571560484479) := by
  decide +kernel

theorem sound028 (hp : 11495562424261 = FastDivSum 1000000000000 55179) :
    (∀ U : ℕ, 55179 ≤ U → U < 59536 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11571560484479 = FastDivSum 1000000000000 59536 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 55179) (h := 11495562424261)
    (rows := rows028) (by decide +kernel) hp checked028
  rw [end028] at hs
  exact hs

theorem prefix028 : 11495562424261 = FastDivSum 1000000000000 55179 :=
  (sound027 prefix027).2

theorem bound028 : ∀ U : ℕ, 2 ≤ U → U < 59536 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 55179
  · exact bound027 U hU hprev
  · exact (sound028 prefix028).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
