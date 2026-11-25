module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block004

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows005 : List Row := greedyEndpointRows 4145 8906994352948 5111

theorem checked005 : CheckRows 1000000000000 4145 8906994352948 rows005 = true := by
  decide +kernel

theorem end005 : RowsEnd 4145 8906994352948 rows005 = (5111, 9116463846291) := by
  decide +kernel

theorem sound005 (hp : 8906994352948 = FastDivSum 1000000000000 4145) :
    (∀ U : ℕ, 4145 ≤ U → U < 5111 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      9116463846291 = FastDivSum 1000000000000 5111 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 4145) (h := 8906994352948)
    (rows := rows005) (by decide +kernel) hp checked005
  rw [end005] at hs
  exact hs

theorem prefix005 : 8906994352948 = FastDivSum 1000000000000 4145 :=
  (sound004 prefix004).2

theorem bound005 : ∀ U : ℕ, 2 ≤ U → U < 5111 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 4145
  · exact bound004 U hU hprev
  · exact (sound005 prefix005).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
