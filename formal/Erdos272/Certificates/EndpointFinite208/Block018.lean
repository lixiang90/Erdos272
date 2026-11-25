module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block017

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows018 : List Row := greedyEndpointRows 23801 10654719536253 26119

theorem checked018 : CheckRows 1000000000000 23801 10654719536253 rows018 = true := by
  decide +kernel

theorem end018 : RowsEnd 23801 10654719536253 rows018 = (26119, 10747653093002) := by
  decide +kernel

theorem sound018 (hp : 10654719536253 = FastDivSum 1000000000000 23801) :
    (∀ U : ℕ, 23801 ≤ U → U < 26119 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10747653093002 = FastDivSum 1000000000000 26119 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 23801) (h := 10654719536253)
    (rows := rows018) (by decide +kernel) hp checked018
  rw [end018] at hs
  exact hs

theorem prefix018 : 10654719536253 = FastDivSum 1000000000000 23801 :=
  (sound017 prefix017).2

theorem bound018 : ∀ U : ℕ, 2 ≤ U → U < 26119 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 23801
  · exact bound017 U hU hprev
  · exact (sound018 prefix018).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
