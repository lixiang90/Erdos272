module

public import Erdos272.Resources.N233811.SourcePayment233811W0
public import Erdos272.Resources.N233811.SourcePayment233811W1
public import Erdos272.Resources.N233811.WindowData233811
public import Erdos272.Resources.N291012.LowResourceBridges3040

@[expose] public section

namespace JSP233.WindowPayment233811
open StarCompletion APGeometry SevenFamily208 SourceData233811W0
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_source_for_proof {N w : ℕ} {A F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (WindowData233811.info w).low ≤ N)
    (hhi : N ≤ (WindowData233811.info w).high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (WindowData233811.info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*WindowData233811.G w*
      (∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+WindowData233811.Fee N w := by
  interval_cases w
  · have hcap : N ≤ 236005 := by simpa [WindowData233811.info] using hhi
    have h := SourcePayment233811W0.actual_source (N := 236005) (by decide) (by decide)
      (LowResourceBridges3040.legal_ambient hcap hlegal) hbad
      (by simpa [WindowData233811.info] using hsize)
      (fun S hS => (hsparse S hS).trans hcap) hAF
    have he : WindowData233811.Fee N 0 = SourceData233811W0.SourceUpper 236005 := by
      simp [WindowData233811.Fee, WindowData233811.FeeA, WindowData233811.FeeB, WindowData233811.FeeC]
    rw [he]
    change _ ≤ 6 * SourceData233811W0.G * _ + _
    exact h
  · have hl : 236005 ≤ N := by simpa [WindowData233811.info] using hlo
    have hh : N ≤ 241005 := by have h := hhi; norm_num [WindowData233811.info] at h; omega
    have h := SourcePayment233811W0.actual_source hl hh hlegal hbad (by simpa [WindowData233811.info] using hsize) hsparse hAF
    have he : WindowData233811.Fee N 1 = SourceData233811W0.SourceUpper N := rfl
    rw [he]
    change _ ≤ 6 * SourceData233811W0.G * _ + _
    exact h

  · have hl : 241006 ≤ N := by simpa [WindowData233811.info] using hlo
    have hh : N ≤ 246006 := by have h := hhi; norm_num [WindowData233811.info] at h; omega
    have h := SourcePayment233811W1.actual_source hl hh hlegal hbad
      (by simpa [WindowData233811.info] using hsize) hsparse hAF
    have he : WindowData233811.Fee N 2 = SourceData233811W1.SourceUpper N := rfl
    rw [he]
    exact h

#print axioms actual_source_for_proof
end
end JSP233.WindowPayment233811
