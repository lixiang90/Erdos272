module

public import Erdos272.Resources.FarJoint112
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section

namespace JSP233.WeightedJoint136
open StarCompletion APGeometry NearAP36 FarSlot112 FarCapacity112 FarJoint112 LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def IntrinsicJointCodes (N D : ℕ) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop) (S : Finset ℤ) :
    Finset (ℕ × (ℤ × ℤ)) :=
  (JointCodes N D core step short S).filter
    (fun q => IntrinsicPair q.2.1 S {q.2.1 + (q.1 : ℤ),q.2.2})

theorem intrinsic_joint_subset {N D : ℕ} (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop) (S : Finset ℤ) :
    IntrinsicJointCodes N D core step short S ⊆ JointCodes N D core step short S :=
  Finset.filter_subset _ _

theorem actual_weighted_fiber_le_two {N D : ℕ} {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} (hF : Legal Ω F)
    (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S)) (q : ℕ × (ℤ × ℤ)) :
    (F.filter (fun S => q ∈ JointCodes N D core step short S)).card +
      (F.filter (fun S => q ∈ IntrinsicJointCodes N D core step short S)).card ≤ 2 := by
  let C := F.filter (fun S => q ∈ JointCodes N D core step short S)
  let I := F.filter (fun S => q ∈ IntrinsicJointCodes N D core step short S)
  have hsub : I ⊆ C := by
    intro S hS
    obtain ⟨hSF,hSI⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,intrinsic_joint_subset core step short S hSI⟩
  by_cases hI : I.Nonempty
  · obtain ⟨S,hS⟩ := hI
    obtain ⟨hSF,hSI⟩ := Finset.mem_filter.mp hS
    obtain ⟨hScode,hSprivate⟩ := Finset.mem_filter.mp hSI
    have hSpoints := joint_code_points (hcore S hSF).1 hScode
    have heq : ∀ T ∈ C, T=S := by
      intro T hT
      obtain ⟨hTF,hTcode⟩ := Finset.mem_filter.mp hT
      by_contra hne
      have hTpoints := joint_code_points (hcore T hTF).1 hTcode
      exact actual_intrinsic_slot_private hF hSF hTF (Ne.symm hne)
        hSpoints.1 hSprivate hTpoints.1 hTpoints.2.1 hTpoints.2.2
    have hc : C.card≤1 := Finset.card_le_one.mpr
      (fun T hT U hU => (heq T hT).trans (heq U hU).symm)
    have hi : I.card≤1 := (Finset.card_le_card hsub).trans hc
    change C.card+I.card≤2
    omega
  · have hi : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hc := actual_joint_fiber_card_le_two (N:=N) (D:=D) hF core step short hcore hAt q
    change C.card+I.card≤2
    rw [hi,Finset.card_empty,Nat.add_zero]
    exact hc

theorem actual_joint_count_of_half_mass {N D μ : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S))
    (hcut : ∀ S ∈ F, ¬short S → 1≤step S ∧ step S≤D)
    (hmass : ∀ S ∈ F, μ≤(JointCodes N D core step short S).card)
    (hhalf : ∀ S ∈ F, (JointCodes N D core step short S).card≤
      2*(IntrinsicJointCodes N D core step short S).card) :
    3*μ*F.card≤4*D*N^2 := by
  let slots := PhysicalSlots N D
  let r : Finset ℤ → (ℕ × (ℤ × ℤ)) → Prop :=
    fun S q => q∈JointCodes N D core step short S
  let m : Finset ℤ → (ℕ × (ℤ × ℤ)) → Prop :=
    fun S q => q∈IntrinsicJointCodes N D core step short S
  have hcodes := joint_codes_subset_slots hF.1 core step short (fun S hS => (hcore S hS).1) hcut
  have hr : ∀ S∈F, slots.bipartiteAbove r S=JointCodes N D core step short S := by
    intro S hS
    ext q
    simp only [Finset.mem_bipartiteAbove]
    exact and_iff_right_of_imp (fun hq => hcodes S hS hq)
  have hm : ∀ S∈F, slots.bipartiteAbove m S=IntrinsicJointCodes N D core step short S := by
    intro S hS
    ext q
    simp only [Finset.mem_bipartiteAbove]
    exact and_iff_right_of_imp (fun hq => hcodes S hS (intrinsic_joint_subset core step short S hq))
  let C := ∑ S∈F,(JointCodes N D core step short S).card
  let I := ∑ S∈F,(IntrinsicJointCodes N D core step short S).card
  have hCr : C=∑q∈slots,(F.filter (fun S=>r S q)).card := by
    calc
      C = ∑S∈F,(slots.bipartiteAbove r S).card :=
        Finset.sum_congr rfl (fun S hS => congrArg Finset.card (hr S hS).symm)
      _ = ∑q∈slots,(F.bipartiteBelow r q).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
      _ = _ := rfl
  have hIm : I=∑q∈slots,(F.filter (fun S=>m S q)).card := by
    calc
      I = ∑S∈F,(slots.bipartiteAbove m S).card :=
        Finset.sum_congr rfl (fun S hS => congrArg Finset.card (hm S hS).symm)
      _ = ∑q∈slots,(F.bipartiteBelow m q).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow m
      _ = _ := rfl
  have hcapacity : C+I≤2*slots.card := by
    rw [hCr,hIm,←Finset.sum_add_distrib]
    calc
      _ ≤ ∑_q∈slots,2 := Finset.sum_le_sum
        (fun q _ => actual_weighted_fiber_le_two hF core step short hcore hAt q)
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul]; omega
  have hhalfTotal : C≤2*I := by
    have hh := Finset.sum_le_sum hhalf
    dsimp only [C,I]
    simpa only [Finset.mul_sum] using hh
  have hmassTotal : μ*F.card≤C := by
    calc
      μ*F.card = ∑_S∈F,μ := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]
      _ ≤ C := Finset.sum_le_sum hmass
  dsimp only [slots] at hcapacity
  rw [physicalSlots_card] at hcapacity
  nlinarith only [hcapacity,hhalfTotal,hmassTotal]

#print axioms intrinsic_joint_subset
#print axioms actual_weighted_fiber_le_two
#print axioms actual_joint_count_of_half_mass
end
end JSP233.WeightedJoint136
