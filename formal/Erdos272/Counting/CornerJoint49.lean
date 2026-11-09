module

public import Erdos272.Resources.PreparedWitness48

@[expose] public section
namespace JSP233.CornerJoint49
open StarCompletion PrivatePairExistence LongTerminal35 WitnessInterval43
open scoped Classical
noncomputable section

def LeftRectangle (N c R : ℕ) : Finset (Finset ℤ) :=
  CrossPairs (Finset.Icc 1 (c:ℤ)) (Finset.Ioc (R:ℤ) N)

def FarRectangle (N L R : ℕ) : Finset (Finset ℤ) :=
  CrossPairs (Finset.Ioc (L:ℤ) R) (Finset.Ioc (R:ℤ) N)

def LeftCorners (F : Finset (Finset ℤ)) (c R : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>(c:ℤ)∈S ∧ ¬IsAP S ∧ ∃x p:ℤ,x<c ∧ (R:ℤ)<p ∧ IntrinsicPair c S {x,p})

def ExteriorRootIntervals (F : Finset (Finset ℤ)) (c R : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>∃a b:ℤ,a<c ∧ (R:ℤ)<b ∧ S=Finset.Icc a b)

def FarCorners (F : Finset (Finset ℤ)) (c L R : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>(c:ℤ)∈S ∧ ¬IsAP S ∧
    ∃x p:ℤ,(L:ℤ)<x ∧ x≤R ∧ (R:ℤ)<p ∧ IntrinsicPair c S {x,p})

theorem left_rectangle_card (N c R : ℕ) : (LeftRectangle N c R).card≤c*(N-R) := by
  have hA : (Finset.Icc (1:ℤ) (c:ℤ)).card=c := by simp only [Int.card_Icc];omega
  have hB : (Finset.Ioc (R:ℤ) (N:ℤ)).card=N-R := by simp only [Int.card_Ioc];omega
  exact (cross_pairs_card_le _ _).trans_eq (by rw [hA,hB])

theorem far_rectangle_card (N L R : ℕ) : (FarRectangle N L R).card≤(R-L)*(N-R) := by
  have hA : (Finset.Ioc (L:ℤ) (R:ℤ)).card=R-L := by simp only [Int.card_Ioc];omega
  have hB : (Finset.Ioc (R:ℤ) (N:ℤ)).card=N-R := by simp only [Int.card_Ioc];omega
  exact (cross_pairs_card_le _ _).trans_eq (by rw [hA,hB])

theorem actual_left_interval_joint {N c R : ℕ} {F C E : Finset (Finset ℤ)}
    (hcR : c≤R) (hF : Legal (Ground N) F) (hCF : C⊆F) (hEF : E⊆F)
    (hc : ∀S∈C,(c:ℤ)∈S) (hbad : ∀S∈C,¬IsAP S)
    (hW : ∀S∈C,∃x p:ℤ,x<c ∧ (R:ℤ)<p ∧ IntrinsicPair c S {x,p})
    (hE : ∀S∈E,∃a b:ℤ,a<c ∧ (R:ℤ)<b ∧ S=Finset.Icc a b) :
    C.card+E.card≤c*(N-R) := by
  have hh : C.card+E.card≤(LeftRectangle N c R).card := by
    apply private_pairs_and_intervals_card_le hF hCF hEF hc hbad
    · intro S hS
      obtain ⟨x,p,hxc,hRp,hw⟩ := hW S hS
      have hx := (mem_ground N x).mp (hF.1 S (hCF hS) (hw.2.2.1 (by simp)))
      have hp := (mem_ground N p).mp (hF.1 S (hCF hS) (hw.2.2.1 (by simp)))
      refine ⟨{x,p},hw,?_⟩
      exact Finset.mem_image.mpr ⟨(x,p),Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hx.1,hxc.le⟩,Finset.mem_Ioc.mpr ⟨hRp,hp.2⟩⟩,rfl⟩
    · intro S hS
      obtain ⟨a,b,hac,hRb,hrep⟩ := hE S hS
      have hcb : (c:ℤ)<b := (show (c:ℤ)≤R by exact_mod_cast hcR).trans_lt hRb
      have hab : a≤b := hac.le.trans hcb.le
      have haS : a∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
      have hbS : b∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
      have ha := (mem_ground N a).mp (hF.1 S (hEF hS) haS)
      have hb := (mem_ground N b).mp (hF.1 S (hEF hS) hbS)
      refine ⟨a,b,hac,hcb,hrep,?_⟩
      exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨ha.1,hac.le⟩,Finset.mem_Ioc.mpr ⟨hRb,hb.2⟩⟩,rfl⟩
  exact hh.trans (left_rectangle_card N c R)

theorem actual_far_corner_rectangle {N c L R : ℕ} {F C : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hCF : C⊆F)
    (hc : ∀S∈C,(c:ℤ)∈S) (hbad : ∀S∈C,¬IsAP S)
    (hW : ∀S∈C,∃x p:ℤ,(L:ℤ)<x ∧ x≤R ∧ (R:ℤ)<p ∧ IntrinsicPair c S {x,p}) :
    C.card≤(R-L)*(N-R) := by
  have hh : C.card+(∅:Finset (Finset ℤ)).card≤(FarRectangle N L R).card := by
    apply private_pairs_and_intervals_card_le hF hCF (Finset.empty_subset F) hc hbad
    · intro S hS
      obtain ⟨x,p,hLx,hxR,hRp,hw⟩ := hW S hS
      have hp := (mem_ground N p).mp (hF.1 S (hCF hS) (hw.2.2.1 (by simp)))
      refine ⟨{x,p},hw,?_⟩
      exact Finset.mem_image.mpr ⟨(x,p),Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hLx,hxR⟩,Finset.mem_Ioc.mpr ⟨hRp,hp.2⟩⟩,rfl⟩
    · intro S hS
      simp only [Finset.notMem_empty] at hS
  simp only [Finset.card_empty,Nat.add_zero] at hh
  exact hh.trans (far_rectangle_card N L R)

theorem actual_left_corners_and_intervals {N c R : ℕ} {F : Finset (Finset ℤ)}
    (hcR : c≤R) (hF : Legal (Ground N) F) :
    (LeftCorners F c R).card+(ExteriorRootIntervals F c R).card≤c*(N-R) := by
  apply actual_left_interval_joint hcR hF (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · intro S hS;exact (Finset.mem_filter.mp hS).2.1
  · intro S hS;exact (Finset.mem_filter.mp hS).2.2.1
  · intro S hS;exact (Finset.mem_filter.mp hS).2.2.2
  · intro S hS;exact (Finset.mem_filter.mp hS).2

theorem actual_far_corners {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) : (FarCorners F c L R).card≤(R-L)*(N-R) := by
  apply actual_far_corner_rectangle hF (Finset.filter_subset _ _)
  · intro S hS;exact (Finset.mem_filter.mp hS).2.1
  · intro S hS;exact (Finset.mem_filter.mp hS).2.2.1
  · intro S hS;exact (Finset.mem_filter.mp hS).2.2.2

theorem actual_selected_left_joint {N c R : ℕ} {F C : Finset (Finset ℤ)}
    (x p : Finset ℤ→ℤ) (hcR : c≤R) (hF : Legal (Ground N) F) (hCF : C⊆F)
    (hc : ∀S∈C,(c:ℤ)∈S) (hbad : ∀S∈C,¬IsAP S)
    (hW : ∀S∈C,IntrinsicPair c S {x S,p S}) :
    (C.filter (fun S=>(R:ℤ)<p S ∧ x S<c)).card+
      (ExteriorRootIntervals F c R).card≤c*(N-R) := by
  apply actual_left_interval_joint hcR hF ((Finset.filter_subset _ _).trans hCF)
    (Finset.filter_subset _ _)
  · intro S hS;exact hc S (Finset.mem_filter.mp hS).1
  · intro S hS;exact hbad S (Finset.mem_filter.mp hS).1
  · intro S hS
    obtain ⟨hSC,hRp,hxc⟩ := Finset.mem_filter.mp hS
    exact ⟨x S,p S,hxc,hRp,hW S hSC⟩
  · intro S hS;exact (Finset.mem_filter.mp hS).2

theorem actual_selected_far_rectangle {N c L R : ℕ} {F C : Finset (Finset ℤ)}
    (x p : Finset ℤ→ℤ) (hF : Legal (Ground N) F) (hCF : C⊆F)
    (hc : ∀S∈C,(c:ℤ)∈S) (hbad : ∀S∈C,¬IsAP S)
    (hW : ∀S∈C,IntrinsicPair c S {x S,p S}) :
    (C.filter (fun S=>(L:ℤ)<x S ∧ x S≤R ∧ (R:ℤ)<p S)).card≤(R-L)*(N-R) := by
  apply actual_far_corner_rectangle hF ((Finset.filter_subset _ _).trans hCF)
  · intro S hS;exact hc S (Finset.mem_filter.mp hS).1
  · intro S hS;exact hbad S (Finset.mem_filter.mp hS).1
  · intro S hS
    obtain ⟨hSC,hLx,hxR,hRp⟩ := Finset.mem_filter.mp hS
    exact ⟨x S,p S,hLx,hxR,hRp,hW S hSC⟩

#print axioms left_rectangle_card
#print axioms far_rectangle_card
#print axioms actual_left_interval_joint
#print axioms actual_far_corner_rectangle
#print axioms actual_left_corners_and_intervals
#print axioms actual_far_corners
#print axioms actual_selected_left_joint
#print axioms actual_selected_far_rectangle
end
end JSP233.CornerJoint49
