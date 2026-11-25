module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block016

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows017 : List Row := greedyEndpointRows 21608 10558057689242 23801

theorem checked017 : CheckRows 1000000000000 21608 10558057689242 rows017 = true := by
  decide +kernel

theorem end017 : RowsEnd 21608 10558057689242 rows017 = (23801, 10654719536253) := by
  decide +kernel

theorem sound017 (hp : 10558057689242 = FastDivSum 1000000000000 21608) :
    (∀ U : ℕ, 21608 ≤ U → U < 23801 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10654719536253 = FastDivSum 1000000000000 23801 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 21608) (h := 10558057689242)
    (rows := rows017) (by decide +kernel) hp checked017
  rw [end017] at hs
  exact hs

theorem prefix017 : 10558057689242 = FastDivSum 1000000000000 21608 :=
  (sound016 prefix016).2

theorem bound017 : ∀ U : ℕ, 2 ≤ U → U < 23801 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 21608
  · exact bound016 U hU hprev
  · exact (sound017 prefix017).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
