module

public import Erdos272.Resources.StarWindow212
public import Erdos272.Counting.N158375.StarMidpoint158375
public import Erdos272.Counting.N86412.StarClasses86412
public import Erdos272.Arithmetic.RecoveryCaps213
public import Erdos272.Resources.N291012.RootModel291012

public import Erdos272.Counting.N67702.LowStepPayment67702

@[expose] public section

namespace JSP233.StarMidpoint67702
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29 DenseDeletion40
open LowSteps32 APGeometry RecoveryCaps213
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option Elab.async false
set_option maxRecDepth 200000

theorem actual_budget_with_low_surpluses (m : ℕ) {N : ℕ} {c : ℤ}
    {F : Finset (Finset ℤ)} (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    (F.card:ℝ)+((∑d∈LowActive m c (APLarge (RootPart F c)),
      ((StepClass (APLarge (RootPart F c)) (trueStep c) (d:ℤ)).card:ℝ))-((m : ℝ)*1000000))/21≤
        (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
          ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 := by
  obtain ⟨k,km,_,paid⟩ := actual_unpaid_steps m hc hF
  have kr : (k : ℝ) ≤ m := by exact_mod_cast km
  linarith only [paid,kr]

#print axioms actual_budget_with_low_surpluses
#print axioms reciprocal_square_tail
#print axioms finite_class_total
#print axioms actual_AP_total
end
end JSP233.StarMidpoint67702
