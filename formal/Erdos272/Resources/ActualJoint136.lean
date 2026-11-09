module

public import Erdos272.Resources.CoreShellHalf136
public import Erdos272.Resources.WeightedJoint136

@[expose] public section
namespace JSP233.ActualJoint136
open StarCompletion APGeometry FarSlot112 FarCapacity112 FarJoint112
open CoreShellHalf136
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem intrinsic_joint_codes_eq (N D:ℕ) (core:Finset ℤ→Finset ℤ)
    (step:Finset ℤ→ℕ) (short:Finset ℤ→Prop) (S:Finset ℤ) :
    WeightedJoint136.IntrinsicJointCodes N D core step short S=
      IntrinsicCodes S (JointCodes N D core step short S) := rfl

theorem actual_joint_count_maximum {N D μ:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (core:Finset ℤ→Finset ℤ)
    (step:Finset ℤ→ℕ) (short:Finset ℤ→Prop)
    (hmax:∀S∈F,MaximumAPCore S (core S))
    (hAt:∀S∈F,∃p,APAt (step S:ℤ) p (core S))
    (hcut:∀S∈F,¬short S→1≤step S ∧ step S≤D)
    (hmass:∀S∈F,μ≤(JointCodes N D core step short S).card) :
    3*μ*F.card≤4*D*N^2 := by
  apply WeightedJoint136.actual_joint_count_of_half_mass hF core step short
    (fun S hS=>maximum_core_is_maximal (hmax S hS)) hAt hcut hmass
  intro S hS
  rw [intrinsic_joint_codes_eq]
  exact actual_joint_half_intrinsic core step short (hmax S hS) (hAt S hS)

#print axioms intrinsic_joint_codes_eq
#print axioms actual_joint_count_maximum
end
end JSP233.ActualJoint136
