module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block032

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows033 : List Row := greedyEndpointRows 79821 11864763796300 85681

theorem checked033 : CheckRows 1000000000000 79821 11864763796300 rows033 = true := by
  decide +kernel

theorem end033 : RowsEnd 79821 11864763796300 rows033 = (85681, 11935607834677) := by
  decide +kernel

theorem sound033 (hp : 11864763796300 = FastDivSum 1000000000000 79821) :
    (∀ U : ℕ, 79821 ≤ U → U < 85681 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11935607834677 = FastDivSum 1000000000000 85681 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 79821) (h := 11864763796300)
    (rows := rows033) (by decide +kernel) hp checked033
  rw [end033] at hs
  exact hs

theorem prefix033 : 11864763796300 = FastDivSum 1000000000000 79821 :=
  (sound032 prefix032).2

theorem bound033 : ∀ U : ℕ, 2 ≤ U → U < 85681 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 79821
  · exact bound032 U hU hprev
  · exact (sound033 prefix033).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
