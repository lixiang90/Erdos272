module

public import Erdos272.Counting.N86412.UniformEval86412
public import Erdos272.Arithmetic.N86412.TotientStrict86412
public import Erdos272.Resources.N86412.SourceContract86412

@[expose] public section

namespace JSP233.UniformSound86412
open StarCompletion SourceBridge208 IntrinsicTriples208 SourceContract86412
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem value_eq_U {s : ℕ} (hs : s ≤ 32753) :
    UniformEval86412.value s = TotientStrict86412.U s := by
  unfold UniformEval86412.value TotientStrict86412.U
  apply Finset.sum_congr rfl
  intro q hq
  have hqs : q ≤ 32753 := by have hh := (Finset.mem_Ico.mp hq).2; omega
  rw [FastDecode208.phi_correct q hqs]

theorem uniform_paid {lower target : ℕ}
    (hlower : 4 ≤ lower) (hcap : lower ≤ 32753)
    (hvalue : target ≤ UniformEval86412.value lower)
    (hpool : ∀ S : Finset ℤ, 4 ≤ S.card → ¬IsAP S → TotientStrict86412.U S.card ≤ (Pool S).card) :
    Paid ⟨lower, 1, target⟩ := by
  intro N S hN hground hS hsize hdefect
  change lower ≤ S.card at hsize
  change 1 ≤ Defect S at hdefect
  change target ≤ (Pool S).card
  have hnot : ¬IsAP S := by
    intro hAP
    have hm := AP_card_le_max hAP (Finset.Subset.refl S)
    unfold Defect at hdefect
    omega
  have hv : target ≤ TotientStrict86412.U lower := by
    simpa only [value_eq_U hcap] using hvalue
  exact hv.trans ((TotientStrict86412.u_mono (by omega) hsize).trans
    (hpool S (hlower.trans hsize) hnot))

#print axioms value_eq_U
#print axioms uniform_paid
end
end JSP233.UniformSound86412
