module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block014

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows015 : List Row := greedyEndpointRows 17623 10354204174156 19557

theorem checked015 : CheckRows 1000000000000 17623 10354204174156 rows015 = true := by
  decide +kernel

theorem end015 : RowsEnd 17623 10354204174156 rows015 = (19557, 10458329779043) := by
  decide +kernel

theorem sound015 (hp : 10354204174156 = FastDivSum 1000000000000 17623) :
    (∀ U : ℕ, 17623 ≤ U → U < 19557 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      10458329779043 = FastDivSum 1000000000000 19557 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 17623) (h := 10354204174156)
    (rows := rows015) (by decide +kernel) hp checked015
  rw [end015] at hs
  exact hs

theorem prefix015 : 10354204174156 = FastDivSum 1000000000000 17623 :=
  (sound014 prefix014).2

theorem bound015 : ∀ U : ℕ, 2 ≤ U → U < 19557 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 17623
  · exact bound014 U hU hprev
  · exact (sound015 prefix015).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
