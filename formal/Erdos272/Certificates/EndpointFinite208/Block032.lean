module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block031

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows032 : List Row := greedyEndpointRows 74277 11792778986795 79821

theorem checked032 : CheckRows 1000000000000 74277 11792778986795 rows032 = true := by
  decide +kernel

theorem end032 : RowsEnd 74277 11792778986795 rows032 = (79821, 11864763796300) := by
  decide +kernel

theorem sound032 (hp : 11792778986795 = FastDivSum 1000000000000 74277) :
    (∀ U : ℕ, 74277 ≤ U → U < 79821 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11864763796300 = FastDivSum 1000000000000 79821 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 74277) (h := 11792778986795)
    (rows := rows032) (by decide +kernel) hp checked032
  rw [end032] at hs
  exact hs

theorem prefix032 : 11792778986795 = FastDivSum 1000000000000 74277 :=
  (sound031 prefix031).2

theorem bound032 : ∀ U : ℕ, 2 ≤ U → U < 79821 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 74277
  · exact bound031 U hU hprev
  · exact (sound032 prefix032).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
