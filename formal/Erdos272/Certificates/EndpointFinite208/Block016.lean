module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block015

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows016 : List Row := greedyEndpointRows 19557 10458329779043 21608

theorem checked016 : CheckRows 1000000000000 19557 10458329779043 rows016 = true := by
  decide +kernel

theorem end016 : RowsEnd 19557 10458329779043 rows016 = (21608, 10558057689242) := by
  decide +kernel

theorem sound016 (hp : 10458329779043 = FastDivSum 1000000000000 19557) :
    (∀ U : ℕ, 19557 ≤ U → U < 21608 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10558057689242 = FastDivSum 1000000000000 21608 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 19557) (h := 10458329779043)
    (rows := rows016) (by decide +kernel) hp checked016
  rw [end016] at hs
  exact hs

theorem prefix016 : 10458329779043 = FastDivSum 1000000000000 19557 :=
  (sound015 prefix015).2

theorem bound016 : ∀ U : ℕ, 2 ≤ U → U < 21608 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 19557
  · exact bound015 U hU hprev
  · exact (sound016 prefix016).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
