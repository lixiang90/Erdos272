module

public import Erdos272.Resources.N109474.RunSource109474

@[expose] public section

namespace JSP233.SourceContract86412
open StarCompletion SourceBridge208 IntrinsicTriples208
noncomputable section
set_option autoImplicit false

structure Contract where
  lower : ℕ
  defect : ℕ
  target : ℕ

def Paid (c : Contract) : Prop :=
  ∀ {N : ℕ} {S : Finset ℤ}, N ≤ 2^18 → S ⊆ Ground N → 2 ≤ S.card →
    c.lower ≤ S.card → c.defect ≤ Defect S → c.target ≤ (Pool S).card

structure CertifiedContract where
  contract : Contract
  actual : Paid contract

theorem weaken_paid (p : CertifiedContract) (c : Contract)
    (hlower : p.contract.lower ≤ c.lower) (hdefect : p.contract.defect ≤ c.defect)
    (htarget : c.target ≤ p.contract.target) : Paid c := by
  intro N S hN hground hS hsize hdef
  exact htarget.trans (p.actual hN hground hS (hlower.trans hsize) (hdefect.trans hdef))

def weaken (p : CertifiedContract) (c : Contract)
    (hlower : p.contract.lower ≤ c.lower) (hdefect : p.contract.defect ≤ c.defect)
    (htarget : c.target ≤ p.contract.target) : CertifiedContract :=
  ⟨c, weaken_paid p c hlower hdefect htarget⟩

#print axioms weaken_paid
end
end JSP233.SourceContract86412
