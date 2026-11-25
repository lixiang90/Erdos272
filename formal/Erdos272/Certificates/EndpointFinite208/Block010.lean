module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block009

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows010 : List Row := greedyEndpointRows 9738 9761058041347 11111

theorem checked010 : CheckRows 1000000000000 9738 9761058041347 rows010 = true := by
  decide +kernel

theorem end010 : RowsEnd 9738 9761058041347 rows010 = (11111, 9892951546922) := by
  decide +kernel

theorem sound010 (hp : 9761058041347 = FastDivSum 1000000000000 9738) :
    (∀ U : ℕ, 9738 ≤ U → U < 11111 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9892951546922 = FastDivSum 1000000000000 11111 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 9738) (h := 9761058041347)
    (rows := rows010) (by decide +kernel) hp checked010
  rw [end010] at hs
  exact hs

theorem prefix010 : 9761058041347 = FastDivSum 1000000000000 9738 :=
  (sound009 prefix009).2

theorem bound010 : ∀ U : ℕ, 2 ≤ U → U < 11111 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 9738
  · exact bound009 U hU hprev
  · exact (sound010 prefix010).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
