module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block029

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows030 : List Row := greedyEndpointRows 64169 11646498932268 69081

theorem checked030 : CheckRows 1000000000000 64169 11646498932268 rows030 = true := by
  decide +kernel

theorem end030 : RowsEnd 64169 11646498932268 rows030 = (69081, 11720257876893) := by
  decide +kernel

theorem sound030 (hp : 11646498932268 = FastDivSum 1000000000000 64169) :
    (∀ U : ℕ, 64169 ≤ U → U < 69081 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11720257876893 = FastDivSum 1000000000000 69081 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 64169) (h := 11646498932268)
    (rows := rows030) (by decide +kernel) hp checked030
  rw [end030] at hs
  exact hs

theorem prefix030 : 11646498932268 = FastDivSum 1000000000000 64169 :=
  (sound029 prefix029).2

theorem bound030 : ∀ U : ℕ, 2 ≤ U → U < 69081 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 64169
  · exact bound029 U hU hprev
  · exact (sound030 prefix030).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
