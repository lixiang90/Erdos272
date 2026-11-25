module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block037

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows038 : List Row := greedyEndpointRows 112833 12210884169037 120646

theorem checked038 : CheckRows 1000000000000 112833 12210884169037 rows038 = true := by
  decide +kernel

theorem end038 : RowsEnd 112833 12210884169037 rows038 = (120646, 12277835666434) := by
  decide +kernel

theorem sound038 (hp : 12210884169037 = FastDivSum 1000000000000 112833) :
    (∀ U : ℕ, 112833 ≤ U → U < 120646 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12277835666434 = FastDivSum 1000000000000 120646 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 112833) (h := 12210884169037)
    (rows := rows038) (by decide +kernel) hp checked038
  rw [end038] at hs
  exact hs

theorem prefix038 : 12210884169037 = FastDivSum 1000000000000 112833 :=
  (sound037 prefix037).2

theorem bound038 : ∀ U : ℕ, 2 ≤ U → U < 120646 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 112833
  · exact bound037 U hU hprev
  · exact (sound038 prefix038).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
