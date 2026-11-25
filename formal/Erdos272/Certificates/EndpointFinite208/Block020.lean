module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block019

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows020 : List Row := greedyEndpointRows 28596 10838255262664 31241

theorem checked020 : CheckRows 1000000000000 28596 10838255262664 rows020 = true := by
  decide +kernel

theorem end020 : RowsEnd 28596 10838255262664 rows020 = (31241, 10926718267834) := by
  decide +kernel

theorem sound020 (hp : 10838255262664 = FastDivSum 1000000000000 28596) :
    (∀ U : ℕ, 28596 ≤ U → U < 31241 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10926718267834 = FastDivSum 1000000000000 31241 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 28596) (h := 10838255262664)
    (rows := rows020) (by decide +kernel) hp checked020
  rw [end020] at hs
  exact hs

theorem prefix020 : 10838255262664 = FastDivSum 1000000000000 28596 :=
  (sound019 prefix019).2

theorem bound020 : ∀ U : ℕ, 2 ≤ U → U < 31241 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 28596
  · exact bound019 U hU hprev
  · exact (sound020 prefix020).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
