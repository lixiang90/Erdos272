module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block026

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows027 : List Row := greedyEndpointRows 51101 11418784769776 55179

theorem checked027 : CheckRows 1000000000000 51101 11418784769776 rows027 = true := by
  decide +kernel

theorem end027 : RowsEnd 51101 11418784769776 rows027 = (55179, 11495562424261) := by
  decide +kernel

theorem sound027 (hp : 11418784769776 = FastDivSum 1000000000000 51101) :
    (∀ U : ℕ, 51101 ≤ U → U < 55179 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11495562424261 = FastDivSum 1000000000000 55179 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 51101) (h := 11418784769776)
    (rows := rows027) (by decide +kernel) hp checked027
  rw [end027] at hs
  exact hs

theorem prefix027 : 11418784769776 = FastDivSum 1000000000000 51101 :=
  (sound026 prefix026).2

theorem bound027 : ∀ U : ℕ, 2 ≤ U → U < 55179 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 51101
  · exact bound026 U hU hprev
  · exact (sound027 prefix027).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
