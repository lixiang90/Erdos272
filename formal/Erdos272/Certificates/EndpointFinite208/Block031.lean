module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block030

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows031 : List Row := greedyEndpointRows 69081 11720257876893 74277

theorem checked031 : CheckRows 1000000000000 69081 11720257876893 rows031 = true := by
  decide +kernel

theorem end031 : RowsEnd 69081 11720257876893 rows031 = (74277, 11792778986795) := by
  decide +kernel

theorem sound031 (hp : 11720257876893 = FastDivSum 1000000000000 69081) :
    (∀ U : ℕ, 69081 ≤ U → U < 74277 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11792778986795 = FastDivSum 1000000000000 74277 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 69081) (h := 11720257876893)
    (rows := rows031) (by decide +kernel) hp checked031
  rw [end031] at hs
  exact hs

theorem prefix031 : 11720257876893 = FastDivSum 1000000000000 69081 :=
  (sound030 prefix030).2

theorem bound031 : ∀ U : ℕ, 2 ≤ U → U < 74277 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 69081
  · exact bound030 U hU hprev
  · exact (sound031 prefix031).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
