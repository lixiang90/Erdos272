module

public import Erdos272.Resources.N86412.SourcePayment86412W2

@[expose] public section

namespace JSP233.SourceAmbient82427
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Constant : ℝ := 6687285737295017569366769/17731000000000000

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hhi : N ≤ 86412) (hlegal : Legal (Ground N) A)
    (hbad : ∀ S ∈ A, ¬IsAP S) (hsize : ∀ S ∈ A, 130 ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*(1/547128 : ℝ)*(∑ S ∈ F, ((Pool S).card : ℝ))+Constant := by
  have hg : Ground N ⊆ Ground 86412 := by
    intro x hx
    have hh := (mem_ground N x).mp hx
    apply (mem_ground 86412 x).mpr
    exact ⟨hh.1,hh.2.trans (by exact_mod_cast hhi)⟩
  have hl : Legal (Ground 86412) A := ⟨fun S hS => (hlegal.1 S hS).trans hg,hlegal.2⟩
  have hb := SourcePayment86412W2.actual_source (N:=86412) (by decide) (by decide)
    hl hbad hsize (fun S hS => (hsparse S hS).trans hhi) hAF
  norm_num [SourceData86412W2.G,SourceData86412W2.SourceUpper,
    SourceData86412W2.CoeffA,SourceData86412W2.CoeffB,SourceData86412W2.CoeffC,Constant] at hb ⊢
  exact hb

#print axioms actual_source
end
end JSP233.SourceAmbient82427
