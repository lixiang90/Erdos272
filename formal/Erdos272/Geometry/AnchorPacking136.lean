module

public import Erdos272.Resources.FarCapacity112

@[expose] public section
namespace JSP233.AnchorPacking136
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Shift (A:Finset ℤ) (g:ℤ) : Finset ℤ := A.image (fun a=>a+g)

theorem shift_card (A:Finset ℤ) (g:ℤ) : (Shift A g).card=A.card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact add_right_cancel hab

theorem shift_disjoint {A:Finset ℤ} {d g:ℤ} (hg:0<g) (hdg:2*g≤d)
    (hgrid:∀a∈A,∀b∈A,d∣a-b) : Disjoint A (Shift A g) := by
  apply Finset.disjoint_left.mpr
  intro a ha hshift
  obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp hshift
  have hh:=hgrid a ha b hb
  have he:a-b=g:=by omega
  rw [he] at hh
  have hsmall:=Int.le_of_dvd hg hh
  omega

theorem paired_card {A:Finset ℤ} {d g:ℤ} (hg:0<g) (hdg:2*g≤d)
    (hgrid:∀a∈A,∀b∈A,d∣a-b) : (A∪Shift A g).card=2*A.card := by
  rw [Finset.card_union_of_disjoint (shift_disjoint hg hdg hgrid),shift_card]
  omega

theorem top_not_paired {A:Finset ℤ} (hA:A.Nonempty) {d g:ℤ}
    (hg:0<g) (hdg:2*g≤d) : A.max' hA+d∉A∪Shift A g := by
  intro h
  rcases Finset.mem_union.mp h with ha|hs
  · have hh:=Finset.le_max' A (A.max' hA+d) ha
    omega
  · obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp hs
    have hh:=Finset.le_max' A b hb
    omega

theorem paired_pack_bound {A U:Finset ℤ} (hA:A.Nonempty) {d g:ℤ}
    (hg:0<g) (hdg:2*g≤d) (hgrid:∀a∈A,∀b∈A,d∣a-b)
    (ha:A⊆U) (hs:Shift A g⊆U) (ht:A.max' hA+d∈U) : 2*A.card+1≤U.card := by
  have hsub:insert (A.max' hA+d) (A∪Shift A g)⊆U :=
    Finset.insert_subset_iff.mpr ⟨ht,Finset.union_subset ha hs⟩
  have hc:=Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (top_not_paired hA hg hdg),paired_card hg hdg hgrid] at hc
  exact hc

theorem pack_into_AP {A U:Finset ℤ} (hA:A.Nonempty) {d g x:ℤ}
    (hg:0<g) (hdg:2*g≤d) (hgd:g∣d) (hgrid:∀a∈A,∀b∈A,d∣a-b)
    (hU:JSP233.APGeometry.APAt g x U) (hl:A.min' hA∈U) (hr:A.max' hA+d∈U) :
    2*A.card+1≤U.card := by
  have hsub:A⊆U := by
    intro a ha
    apply JSP233.APGeometry.apAt_fill hU hl hr (Finset.min'_le A a ha)
    · have hh:=Finset.le_max' A a ha
      omega
    · exact dvd_trans hgd (hgrid a ha (A.min' hA) (Finset.min'_mem A hA))
  have hshift:Shift A g⊆U := by
    intro y hy
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hy
    apply JSP233.APGeometry.apAt_fill hU hl hr
    · have hh:=Finset.min'_le A a ha
      omega
    · have hh:=Finset.le_max' A a ha
      omega
    · rw [show a+g-A.min' hA=(a-A.min' hA)+g by ring]
      exact dvd_add (dvd_trans hgd (hgrid a ha (A.min' hA) (Finset.min'_mem A hA))) (dvd_refl g)
  exact paired_pack_bound hA hg hdg hgrid hsub hshift hr

#print axioms shift_card
#print axioms shift_disjoint
#print axioms paired_card
#print axioms top_not_paired
#print axioms paired_pack_bound
#print axioms pack_into_AP
end
end JSP233.AnchorPacking136
