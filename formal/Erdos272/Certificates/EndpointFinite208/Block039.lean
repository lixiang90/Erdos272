module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block038

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows039 : List Row := greedyEndpointRows 120646 12277835666434 128961

theorem checked039 : CheckRows 1000000000000 120646 12277835666434 rows039 = true := by
  decide +kernel

theorem end039 : RowsEnd 120646 12277835666434 rows039 = (128961, 12344484790341) := by
  decide +kernel

theorem sound039 (hp : 12277835666434 = FastDivSum 1000000000000 120646) :
    (∀ U : ℕ, 120646 ≤ U → U < 128961 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12344484790341 = FastDivSum 1000000000000 128961 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 120646) (h := 12277835666434)
    (rows := rows039) (by decide +kernel) hp checked039
  rw [end039] at hs
  exact hs

theorem prefix039 : 12277835666434 = FastDivSum 1000000000000 120646 :=
  (sound038 prefix038).2

theorem bound039 : ∀ U : ℕ, 2 ≤ U → U < 128961 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 120646
  · exact bound038 U hU hprev
  · exact (sound039 prefix039).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
