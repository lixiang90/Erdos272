module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block008

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows009 : List Row := greedyEndpointRows 8461 9620497403306 9738

theorem checked009 : CheckRows 1000000000000 8461 9620497403306 rows009 = true := by
  decide +kernel

theorem end009 : RowsEnd 8461 9620497403306 rows009 = (9738, 9761058041347) := by
  decide +kernel

theorem sound009 (hp : 9620497403306 = FastDivSum 1000000000000 8461) :
    (∀ U : ℕ, 8461 ≤ U → U < 9738 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9761058041347 = FastDivSum 1000000000000 9738 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 8461) (h := 9620497403306)
    (rows := rows009) (by decide +kernel) hp checked009
  rw [end009] at hs
  exact hs

theorem prefix009 : 9620497403306 = FastDivSum 1000000000000 8461 :=
  (sound008 prefix008).2

theorem bound009 : ∀ U : ℕ, 2 ≤ U → U < 9738 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 8461
  · exact bound008 U hU hprev
  · exact (sound009 prefix009).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
