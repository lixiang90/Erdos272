module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block023

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows024 : List Row := greedyEndpointRows 40288 11181036992577 43681

theorem checked024 : CheckRows 1000000000000 40288 11181036992577 rows024 = true := by
  decide +kernel

theorem end024 : RowsEnd 40288 11181036992577 rows024 = (43681, 11261895593981) := by
  decide +kernel

theorem sound024 (hp : 11181036992577 = FastDivSum 1000000000000 40288) :
    (∀ U : ℕ, 40288 ≤ U → U < 43681 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11261895593981 = FastDivSum 1000000000000 43681 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 40288) (h := 11181036992577)
    (rows := rows024) (by decide +kernel) hp checked024
  rw [end024] at hs
  exact hs

theorem prefix024 : 11181036992577 = FastDivSum 1000000000000 40288 :=
  (sound023 prefix023).2

theorem bound024 : ∀ U : ℕ, 2 ≤ U → U < 43681 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 40288
  · exact bound023 U hU hprev
  · exact (sound024 prefix024).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
