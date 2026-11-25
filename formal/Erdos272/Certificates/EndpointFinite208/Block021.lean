module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block020

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows021 : List Row := greedyEndpointRows 31241 10926718267834 34082

theorem checked021 : CheckRows 1000000000000 31241 10926718267834 rows021 = true := by
  decide +kernel

theorem end021 : RowsEnd 31241 10926718267834 rows021 = (34082, 11013754983331) := by
  decide +kernel

theorem sound021 (hp : 10926718267834 = FastDivSum 1000000000000 31241) :
    (∀ U : ℕ, 31241 ≤ U → U < 34082 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      11013754983331 = FastDivSum 1000000000000 34082 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 31241) (h := 10926718267834)
    (rows := rows021) (by decide +kernel) hp checked021
  rw [end021] at hs
  exact hs

theorem prefix021 : 10926718267834 = FastDivSum 1000000000000 31241 :=
  (sound020 prefix020).2

theorem bound021 : ∀ U : ℕ, 2 ≤ U → U < 34082 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 31241
  · exact bound020 U hU hprev
  · exact (sound021 prefix021).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
