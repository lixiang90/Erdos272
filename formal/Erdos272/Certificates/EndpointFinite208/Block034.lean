module

public meta import Erdos272.Certificates.EndpointFinite208.GreedyRows
public import Erdos272.Certificates.EndpointFinite208.Block033

@[expose] public section

namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

def rows034 : List Row := greedyEndpointRows 85681 11935607834677 91891

theorem checked034 : CheckRows 1000000000000 85681 11935607834677 rows034 = true := by
  decide +kernel

theorem end034 : RowsEnd 85681 11935607834677 rows034 = (91891, 12005579431884) := by
  decide +kernel

theorem sound034 (hp : 11935607834677 = FastDivSum 1000000000000 85681) :
    (∀ U : ℕ, 85681 ≤ U → U < 91891 → (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      12005579431884 = FastDivSum 1000000000000 91891 := by
  have hs := checked_rows_sound (G := 1000000000000) (a := 85681) (h := 11935607834677)
    (rows := rows034) (by decide +kernel) hp checked034
  rw [end034] at hs
  exact hs

theorem prefix034 : 11935607834677 = FastDivSum 1000000000000 85681 :=
  (sound033 prefix033).2

theorem bound034 : ∀ U : ℕ, 2 ≤ U → U < 91891 →
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  intro U hU hmax
  by_cases hprev : U < 85681
  · exact bound033 U hU hprev
  · exact (sound034 prefix034).1 U (by omega) hmax

end
end JSP233.EndpointFinite208
