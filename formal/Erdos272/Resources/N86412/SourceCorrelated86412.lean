module

public import Erdos272.Resources.N86412.SourceContract86412
public import Erdos272.Resources.N86412.CorrelatedSource86412

@[expose] public section

namespace JSP233.SourceCorrelated86412
open SourceContract86412 StarCompletion SourceBridge208 IntrinsicTriples208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ofPlan (q : CorrelatedSource158375.Plan) : Contract := ⟨q.lower, q.defect, q.target⟩

theorem standard_paid (q : CorrelatedSource109474.Plan)
    (hq : CorrelatedSource109474.Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) : Paid (ofPlan q) := by
  intro N S hN hground hS hsize hdef
  apply CorrelatedSource109474.actual_plan_source_of_high q hq hN hground hS hsize hdef
  intro hhigh
  exact htarget.trans (high.actual hN hground hS (hlower.trans hsize) (hdefect.trans hhigh))

theorem dynamic_paid (q : CorrelatedSource86412.Plan)
    (hq : CorrelatedSource86412.Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) : Paid (ofPlan q) := by
  intro N S hN hground hS hsize hdef
  apply CorrelatedSource86412.actual_plan_source_of_high q hq hN hground hS hsize hdef
  intro hhigh
  exact htarget.trans (high.actual hN hground hS (hlower.trans hsize) (hdefect.trans hhigh))

def standard (q : CorrelatedSource109474.Plan)
    (hq : CorrelatedSource109474.Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) : CertifiedContract :=
  ⟨ofPlan q, standard_paid q hq high hlower hdefect htarget⟩

def dynamic (q : CorrelatedSource86412.Plan)
    (hq : CorrelatedSource86412.Conditions q) (high : CertifiedContract)
    (hlower : high.contract.lower ≤ q.lower) (hdefect : high.contract.defect ≤ q.cutoff)
    (htarget : q.target ≤ high.contract.target) : CertifiedContract :=
  ⟨ofPlan q, dynamic_paid q hq high hlower hdefect htarget⟩

#print axioms standard_paid
#print axioms dynamic_paid
end
end JSP233.SourceCorrelated86412
