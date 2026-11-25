module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block034

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows035 : List Row := greedyEndpointRows 91891 12005579431884 98463

theorem checked035 : CheckRows 1000000000000 91891 12005579431884 rows035 = true := by
  decide +kernel

theorem end035 : RowsEnd 91891 12005579431884 rows035 = (98463, 12074656816489) := by
  decide +kernel

theorem sound035 (hp : 12005579431884 = FastDivSum 1000000000000 91891) :
    (∀ U : ℕ, 91891 ≤ U → U < 98463 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12074656816489 = FastDivSum 1000000000000 98463 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 91891) (h := 12005579431884)
    (rows := rows035) (by decide +kernel) hp checked035
  rw [end035] at hs
  exact hs

theorem prefix035 : 12005579431884 = FastDivSum 1000000000000 91891 :=
  (sound034 prefix034).2

theorem bound035 : ∀ U : ℕ, 2 ≤ U → U < 98463 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 91891
  · exact bound034 U hU hprev
  · exact (sound035 prefix035).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
