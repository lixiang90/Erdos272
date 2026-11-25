module

public import Erdos272.Counting.N67702.RightJoint67702
public import Erdos272.Resources.LocalRecovery208

@[expose] public section

namespace JSP233.PreparedJoint67702
open StarCompletion APGeometry APPrepare49 PreparedWitness48 PreparedClasses50
open LongTerminal35 RestrictedWitness44 PrivatePairExistence
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_prepared_right_joint {N c L R : ℕ} {G : Finset (Finset ℤ)}
    (x p : Finset ℤ→ℤ) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hW : ∀S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S} ∧
      ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) :
    (CQ (PreparedCrooked G c L) x p c L R).card+(EP (PreparedAP G c L) c R).card+1≤
      (L-c)*(N-R)+(L-c) := by
  let C := PreparedCrooked G c L
  let E := PreparedAP G c L
  have hCG : C⊆G := (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hEG : E⊆G := fun _ hS=>(actual_prepared_AP_member hS).1
  have hbad : ∀S∈C,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
  apply RightJoint67702.actual_CQ_EP_joint hcL hLR hRN hG
    ((Finset.filter_subset _ _).trans hCG) ((Finset.filter_subset _ _).trans hEG)
    (fun S hS=>hroot S (hCG (Finset.mem_filter.mp hS).1) (hbad S (Finset.mem_filter.mp hS).1))
    x p APCount41.Low APCount41.High
  · intro S hS
    obtain ⟨hSC,hRp,hcx,hxL⟩ := Finset.mem_filter.mp hS
    have hw := (hW S hSC).1
    have hpN := ((mem_ground N (p S)).mp (hG.1 S (hCG hSC) (hw.2.2.1 (by simp)))).2
    exact ⟨hcx,hxL,hRp,hpN,hw,(hW S hSC).2 hcx hxL hRp⟩
  · intro S hS
    exact actual_EP_interval hG (by omega) houtside hS

#print axioms actual_prepared_right_joint
end
end JSP233.PreparedJoint67702
