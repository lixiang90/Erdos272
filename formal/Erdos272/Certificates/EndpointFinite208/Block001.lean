module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block000

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows001 : List Row := greedyEndpointRows 814 7279790155404 1583

theorem checked001 : CheckRows 1000000000000 814 7279790155404 rows001 = true := by
  decide +kernel

theorem end001 : RowsEnd 814 7279790155404 rows001 = (1583, 7944608546803) := by
  decide +kernel

theorem sound001 (hp : 7279790155404 = FastDivSum 1000000000000 814) :
    (∀ U : ℕ, 814 ≤ U → U < 1583 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      7944608546803 = FastDivSum 1000000000000 1583 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 814) (h := 7279790155404)
    (rows := rows001) (by decide +kernel) hp checked001
  rw [end001] at hs
  exact hs

theorem prefix001 : 7279790155404 = FastDivSum 1000000000000 814 :=
  (sound000 prefix000).2

theorem bound001 : ∀ U : ℕ, 2 ≤ U → U < 1583 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 814
  · exact bound000 U hU hprev
  · exact (sound001 prefix001).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
