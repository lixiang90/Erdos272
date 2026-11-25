module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block018

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows019 : List Row := greedyEndpointRows 26119 10747653093002 28596

theorem checked019 : CheckRows 1000000000000 26119 10747653093002 rows019 = true := by
  decide +kernel

theorem end019 : RowsEnd 26119 10747653093002 rows019 = (28596, 10838255262664) := by
  decide +kernel

theorem sound019 (hp : 10747653093002 = FastDivSum 1000000000000 26119) :
    (∀ U : ℕ, 26119 ≤ U → U < 28596 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10838255262664 = FastDivSum 1000000000000 28596 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 26119) (h := 10747653093002)
    (rows := rows019) (by decide +kernel) hp checked019
  rw [end019] at hs
  exact hs

theorem prefix019 : 10747653093002 = FastDivSum 1000000000000 26119 :=
  (sound018 prefix018).2

theorem bound019 : ∀ U : ℕ, 2 ≤ U → U < 28596 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 26119
  · exact bound018 U hU hprev
  · exact (sound019 prefix019).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
