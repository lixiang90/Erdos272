module

public import Mathlib.Data.Finset.Prod
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section

/-! Pure finite rectangular packing with an explicit missing-point slack.  The actual AP intersection argument
that makes the rectangles disjoint is a separate geometric obligation. -/
namespace JSP233.RectSlack117
open scoped BigOperators
noncomputable section

theorem rectangle_mass_lower {A B S : Finset ℤ} {w b : ℕ}
    (hAB : Disjoint A B)
    (hwc : A.card+B.card+1=w)
    (hA : 50*b+w≤50*A.card) (hB : 50*b+w≤50*B.card) (hmiss : ((A∪B)\S).card≤b) :
    A.card*B.card≤25*(S∩A).card*(S∩B).card := by
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
  · have hba : 25*b≤24*A.card := by omega
    have hm := Nat.mul_le_mul_right (B\S).card hab
    have hs := Nat.mul_le_mul_left B.card hsum
    have hp := Nat.mul_le_mul_left B.card hba
    have huv : 0≤(A\S).card*(B\S).card := Nat.zero_le _
    nlinarith only [hca,hcb,hm,hs,hp,huv]
  · have hba' : B.card≤A.card := by omega
    have hbb : 25*b≤24*B.card := by omega
    have hm := Nat.mul_le_mul_right (A\S).card hba'
    have hs := Nat.mul_le_mul_left A.card hsum
    have hp := Nat.mul_le_mul_left A.card hbb
    have huv : 0≤(A\S).card*(B\S).card := Nat.zero_le _
    nlinarith only [hca,hcb,hm,hs,hp,huv]

theorem disjoint_rectangle_sum_le {A B : Finset ℤ} {E : Finset (Finset ℤ)}
    (hrect : ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩A).product (S∩B)) ((T∩A).product (T∩B))) :
    (∑S∈E,(S∩A).card*(S∩B).card)≤A.card*B.card := by
  classical
  have hp : (E:Set (Finset ℤ)).Pairwise (fun S T=>
      Disjoint ((S∩A).product (S∩B)) ((T∩A).product (T∩B))) := by
    intro S hS T hT hne
    exact hrect S hS T hT hne
  have hs : E.biUnion (fun S=>(S∩A).product (S∩B))⊆A.product B := by
    intro q hq
    obtain ⟨S,_hS,hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hq
    exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp ha).2,(Finset.mem_inter.mp hb).2⟩
  have hh := Finset.card_le_card hs
  rw [Finset.card_biUnion hp] at hh
  simpa only [Finset.product_eq_sprod,Finset.card_product] using hh

theorem actual_rectangles_card_le25 {A B : Finset ℤ} {E : Finset (Finset ℤ)}
    {w b : ℕ} (hw : 0<w) (hAB : Disjoint A B)
    (hwc : A.card+B.card+1=w)
    (hA : 50*b+w≤50*A.card) (hB : 50*b+w≤50*B.card)
    (hmiss : ∀S∈E,((A∪B)\S).card≤b)
    (hrect : ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩A).product (S∩B)) ((T∩A).product (T∩B))) :
    E.card≤25 := by
  classical
  have ha : 0<A.card := by omega
  have hb' : 0<B.card := by omega
  have hab : 0<A.card*B.card := Nat.mul_pos ha hb'
  have hm := Finset.sum_le_sum (fun S hS=>rectangle_mass_lower hAB hwc hA hB (hmiss S hS))
  have hs := disjoint_rectangle_sum_le hrect
  have hm' : E.card*(A.card*B.card)≤25*(∑S∈E,(S∩A).card*(S∩B).card) := by
    simpa only [Finset.sum_const,smul_eq_mul,
      ←Finset.mul_sum,mul_assoc] using hm
  have ht := hm'.trans (Nat.mul_le_mul_left 25 hs)
  nlinarith only [ht,hab]

theorem actual_rectangles_card_le32 {A B : Finset ℤ} {E : Finset (Finset ℤ)}
    {w b : ℕ} (hw : 0<w) (hAB : Disjoint A B)
    (hwc : A.card+B.card+1=w)
    (hA : 50*b+w≤50*A.card) (hB : 50*b+w≤50*B.card)
    (hmiss : ∀S∈E,((A∪B)\S).card≤b)
    (hrect : ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩A).product (S∩B)) ((T∩A).product (T∩B))) :
    E.card≤32 := (actual_rectangles_card_le25 hw hAB hwc hA hB hmiss hrect).trans (by decide)

#print axioms rectangle_mass_lower
#print axioms disjoint_rectangle_sum_le
#print axioms actual_rectangles_card_le25
#print axioms actual_rectangles_card_le32
end
end JSP233.RectSlack117
