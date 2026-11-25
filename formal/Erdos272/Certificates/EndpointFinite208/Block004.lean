module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block003

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows004 : List Row := greedyEndpointRows 3241 8661007131990 4145

theorem checked004 : CheckRows 1000000000000 3241 8661007131990 rows004 = true := by
  decide +kernel

theorem end004 : RowsEnd 3241 8661007131990 rows004 = (4145, 8906994352948) := by
  decide +kernel

theorem sound004 (hp : 8661007131990 = FastDivSum 1000000000000 3241) :
    (∀ U : ℕ, 3241 ≤ U → U < 4145 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      8906994352948 = FastDivSum 1000000000000 4145 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 3241) (h := 8661007131990)
    (rows := rows004) (by decide +kernel) hp checked004
  rw [end004] at hs
  exact hs

theorem prefix004 : 8661007131990 = FastDivSum 1000000000000 3241 :=
  (sound003 prefix003).2

theorem bound004 : ∀ U : ℕ, 2 ≤ U → U < 4145 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 3241
  · exact bound003 U hU hprev
  · exact (sound004 prefix004).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
