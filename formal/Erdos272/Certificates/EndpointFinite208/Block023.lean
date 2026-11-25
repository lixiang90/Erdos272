module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block022

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows023 : List Row := greedyEndpointRows 37096 11098493551283 40288

theorem checked023 : CheckRows 1000000000000 37096 11098493551283 rows023 = true := by
  decide +kernel

theorem end023 : RowsEnd 37096 11098493551283 rows023 = (40288, 11181036992577) := by
  decide +kernel

theorem sound023 (hp : 11098493551283 = FastDivSum 1000000000000 37096) :
    (∀ U : ℕ, 37096 ≤ U → U < 40288 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11181036992577 = FastDivSum 1000000000000 40288 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 37096) (h := 11098493551283)
    (rows := rows023) (by decide +kernel) hp checked023
  rw [end023] at hs
  exact hs

theorem prefix023 : 11098493551283 = FastDivSum 1000000000000 37096 :=
  (sound022 prefix022).2

theorem bound023 : ∀ U : ℕ, 2 ≤ U → U < 40288 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 37096
  · exact bound022 U hU hprev
  · exact (sound023 prefix023).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
