module

public import Erdos272.Global.N82427.WindowPayment82427

@[expose] public section

namespace JSP233.PointSource82426
open StarCompletion APGeometry IntrinsicTriples208 WindowData82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

def LiveWindow (w : ℕ) : Prop := w=0 ∨ w=2 ∨ w=3

def PointFee (w : ℕ) : ℝ := Fee w 82427

theorem actual_source {w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : LiveWindow w) (hlegal : Legal (Ground 82426) A)
    (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ 82426) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((Pool S).card : ℝ))+PointFee w := by
  have hground : Ground 82426 ⊆ Ground 82427 := by
    intro x hx
    have hh := (mem_ground 82426 x).mp hx
    exact (mem_ground 82427 x).mpr ⟨hh.1, hh.2.trans (by norm_num)⟩
  have hlegal' : Legal (Ground 82427) A :=
    ⟨fun S hS => (hlegal.1 S hS).trans hground, hlegal.2⟩
  have hw' : w<4 := by rcases hw with rfl | rfl | rfl <;> decide
  have hlo : (info w).low≤82427 := by
    rcases hw with rfl | rfl | rfl <;> norm_num [info]
  have hhi : 82427≤(info w).high := by
    rcases hw with rfl | rfl | rfl <;> norm_num [info]
  exact WindowPayment82427.actual_source_for_proof hw' hlo hhi hlegal' hbad hsize
    (fun S hS => (hsparse S hS).trans (by decide)) hAF

#print axioms actual_source
end
end JSP233.PointSource82426
