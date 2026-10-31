import Erdos272.Resources.RectSlack137
namespace JSP233.RectSlack140
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
theorem rectangle_mass_lower {A B S : Finset ℤ} {w b : ℕ}
    (hAB : Disjoint A B)
    (hwc : A.card+B.card+1=w)
    (hA : 6000*b+w≤6000*A.card) (hB : 6000*b+w≤6000*B.card) (hmiss : ((A∪B)\S).card≤b) :
    A.card*B.card≤3000*(S∩A).card*(S∩B).card := by
  classical
  have hsplit : (A\S).card+(B\S).card=((A∪B)\S).card := by
    have hd : Disjoint (A\S) (B\S) :=
      Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)
    rw [←Finset.card_union_of_disjoint hd]
    congr 1
    ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hca := Finset.card_sdiff_add_card_inter A S
  have hcb := Finset.card_sdiff_add_card_inter B S
  rw [Finset.inter_comm A S] at hca
  rw [Finset.inter_comm B S] at hcb
  have hsum : (A\S).card+(B\S).card≤b := by omega
  by_cases hab : A.card≤B.card
  · have hba : 3000*b≤2999*A.card := by omega
    have hm := Nat.mul_le_mul_right (B\S).card hab
    have hs := Nat.mul_le_mul_left B.card hsum
    have hp := Nat.mul_le_mul_left B.card hba
    have huv : 0≤(A\S).card*(B\S).card := Nat.zero_le _
    nlinarith only [hca,hcb,hm,hs,hp,huv]
  · have hba' : B.card≤A.card := by omega
    have hbb : 3000*b≤2999*B.card := by omega
    have hm := Nat.mul_le_mul_right (A\S).card hba'
    have hs := Nat.mul_le_mul_left A.card hsum
    have hp := Nat.mul_le_mul_left A.card hbb
    have huv : 0≤(A\S).card*(B\S).card := Nat.zero_le _
    nlinarith only [hca,hcb,hm,hs,hp,huv]

theorem actual_rectangles_card_le3000 {A B : Finset ℤ} {E : Finset (Finset ℤ)}
    {w b : ℕ} (hw : 0<w) (hAB : Disjoint A B)
    (hwc : A.card+B.card+1=w)
    (hA : 6000*b+w≤6000*A.card) (hB : 6000*b+w≤6000*B.card)
    (hmiss : ∀S∈E,((A∪B)\S).card≤b)
    (hrect : ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩A).product (S∩B)) ((T∩A).product (T∩B))) :
    E.card≤3000 := by
  classical
  have ha : 0<A.card := by omega
  have hb' : 0<B.card := by omega
  have hab : 0<A.card*B.card := Nat.mul_pos ha hb'
  have hm := Finset.sum_le_sum (fun S hS=>rectangle_mass_lower hAB hwc hA hB (hmiss S hS))
  have hs := RectSlack137.disjoint_rectangle_sum_le hrect
  have hm' : E.card*(A.card*B.card)≤3000*(∑S∈E,(S∩A).card*(S∩B).card) := by
    simpa only [Finset.sum_const,smul_eq_mul,
      ←Finset.mul_sum,mul_assoc] using hm
  have ht := hm'.trans (Nat.mul_le_mul_left 3000 hs)
  nlinarith only [ht,hab]


#print axioms rectangle_mass_lower
#print axioms actual_rectangles_card_le3000
end
end JSP233.RectSlack140
