module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block010

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows011 : List Row := greedyEndpointRows 11111 9892951546922 12583

theorem checked011 : CheckRows 1000000000000 11111 9892951546922 rows011 = true := by
  decide +kernel

theorem end011 : RowsEnd 11111 9892951546922 rows011 = (12583, 10017357370059) := by
  decide +kernel

theorem sound011 (hp : 9892951546922 = FastDivSum 1000000000000 11111) :
    (∀ U : ℕ, 11111 ≤ U → U < 12583 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10017357370059 = FastDivSum 1000000000000 12583 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 11111) (h := 9892951546922)
    (rows := rows011) (by decide +kernel) hp checked011
  rw [end011] at hs
  exact hs

theorem prefix011 : 9892951546922 = FastDivSum 1000000000000 11111 :=
  (sound010 prefix010).2

theorem bound011 : ∀ U : ℕ, 2 ≤ U → U < 12583 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 11111
  · exact bound010 U hU hprev
  · exact (sound011 prefix011).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
