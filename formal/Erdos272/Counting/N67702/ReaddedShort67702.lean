module

public import Erdos272.Counting.N67702.TwoEndShort67702
public import Erdos272.Counting.N67702.SmallRoot67702

@[expose] public section

namespace JSP233.ReaddedShort67702
open StarCompletion APGeometry APPrepare49 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_small_twoend {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c : ℤ)∈Ground N) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hG : Legal (Ground N) G) (hP : P∈G) (hcP : (c : ℤ)∉P)
    (hLP : ∀z∈P,(L : ℤ)≤z) (hT : T∈G) (hcT : (c : ℤ)∉T)
    (hTR : ∀z∈T,z≤(R : ℤ)) (hsmall : ∀S∈SmallAP G,(c : ℤ)∈S) :
    ((SmallAP G).card : ℝ)≤(3/2 : ℝ)*N-(L : ℝ)/2-
      ((L : ℝ)+((N : ℝ)-R))+c+1 := by
  have hmem := fun S hS=>actual_small_AP_member (F:=G) (S:=S) hS
  have hmeet : ∀ S∈SmallAP G,∀ U∈G,(c : ℤ)∉U→∃z∈S,z∈U := by
    intro S hS U hU hcU
    have hSU : S≠U := by intro he;exact hcU (he ▸ hsmall S hS)
    obtain ⟨z,hz⟩ := isAP_nonempty (hG.2 S (hmem S hS).1 U hU hSU)
    exact ⟨z,(Finset.mem_inter.mp hz).1,(Finset.mem_inter.mp hz).2⟩
  apply TwoEndShort67702.actual_small_count hc hcL hLR hRN
    (fun S hS=>hG.1 S (hmem S hS).1)
    (fun S hS=>(hmem S hS).2.1) (fun S hS=>(hmem S hS).2.2) hsmall
  · intro S hS
    obtain ⟨z,hz,hzP⟩ := hmeet S hS P hP hcP
    exact ⟨z,hz,hLP z hzP⟩
  · intro S hS
    obtain ⟨z,hz,hzT⟩ := hmeet S hS T hT hcT
    exact ⟨z,hz,by intro he;exact hcT (he ▸ hzT),hTR z hzT⟩

theorem actual_readded_small {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 56400≤N) (hhigh : N≤88403)
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) (hspan : L+3≤R) :
    ((SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ))).card : ℝ)≤
      (3/2 : ℝ)*N-(L : ℝ)/2-Width N L R+c+1 := by
  let G := GenericRecovery291012.Readded N 12 F (c : ℤ)
  have hGF : G⊆F := Finset.sdiff_subset
  have hG : Legal (Ground N) G :=
    ⟨fun S hS=>g.legal.1 S (hGF hS),fun S hS U hU hne=>g.legal.2 S (hGF hS) U (hGF hU) hne⟩
  have hs := GenericRecovery291012.actual_retained_subset_readded N 12 F (c : ℤ)
  exact actual_small_twoend g.root_mem g.root_left g.left_right g.right_ground hG
    (hs g.right_member) g.right_avoids g.right_lower (hs g.left_member) g.left_avoids g.left_upper
    (SmallRoot67702.actual_small_root g hN hhigh hleft hspan)

#print axioms actual_small_twoend
#print axioms actual_readded_small
end
end JSP233.ReaddedShort67702
