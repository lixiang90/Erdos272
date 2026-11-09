module

public import Erdos272.Resources.N243614.Layer243614
public import Erdos272.Resources.N243614.SourceWindowData243614
public import Erdos272.Resources.N243614.WindowData243614
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.WindowPayment243614
open StarCompletion APGeometry SevenFamily208 SourceWindowData243614
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 5,
  (Psi (i+1)-Psi i)*Layer243614.Upper N i)

theorem fee (N : ℕ) : Weighted N = SourceUpper N := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Layer243614.Upper, CleanupRows243614.data,
    CleanupRows243614.data00, CleanupRows243614.data01, CleanupRows243614.data02,
    CleanupRows243614.data03, CleanupRows243614.data04, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (hlo : 246007 ≤ N) (hhi : N ≤ 251007)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 148 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi, 5, psi_mono, psi_zero, reciprocal, ?_⟩
  have hs : (∑ i ∈ Finset.range 5, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 5, (Psi (i+1)-Psi i)*Layer243614.Upper N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi5 := Finset.mem_range.mp hi
    have hl := links hi5
    have hb := Layer243614.actual_upper (N := N) (k := i) (ell := i) (psi := Psi)
      hi5 (by simpa only [hl.1] using hlo)
      (by simpa only [hl.2.1] using hhi) hlegal hbad
      (by simpa only [hl.2.2.1] using hsize) hsparse
      (by dsimp only [Psi]; exact_mod_cast hl.2.2.2)
    exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have h := g_positive; positivity)
  change _ ≤ SourceUpper N
  exact hp.trans_eq (fee N)

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 246007 ≤ N) (hhi : N ≤ 251007)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 148 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+SourceUpper N := by
  have hb := SevenFamily208.actual_unit_source hAF g_positive.le
    (actual_obligation hlo hhi hlegal hbad hsize hsparse)
  simpa only [SourceUpper, add_assoc] using hb

theorem actual_source_for_proof {N w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 2) (hlo : (WindowData243614.info w).low ≤ N)
    (hhi : N ≤ (WindowData243614.info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (WindowData243614.info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*WindowData243614.G w*
      (∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+WindowData243614.Fee N w := by
  interval_cases w
  · have hcap : N ≤ 246007 := by simpa [WindowData243614.info] using hhi
    have h := actual_source (N := 246007) (by decide) (by decide)
      (LowResourceBridges3040.legal_ambient hcap hlegal) hbad
      (by simpa [WindowData243614.info] using hsize)
      (fun S hS => (hsparse S hS).trans hcap) hAF
    have he : WindowData243614.Fee N 0 = SourceUpper 246007 := by
      simp [WindowData243614.Fee, WindowData243614.FeeA, WindowData243614.FeeB, WindowData243614.FeeC]
    rw [he]
    exact h
  · have hl : 246007 ≤ N := by simpa [WindowData243614.info] using hlo
    have hh : N ≤ 251007 := by have h := hhi; norm_num [WindowData243614.info] at h; omega
    have h := actual_source hl hh hlegal hbad (by simpa [WindowData243614.info] using hsize) hsparse hAF
    have he : WindowData243614.Fee N 1 = SourceUpper N := rfl
    rw [he]
    exact h

#print axioms fee
#print axioms actual_obligation
#print axioms actual_source
#print axioms actual_source_for_proof
end
end JSP233.WindowPayment243614
