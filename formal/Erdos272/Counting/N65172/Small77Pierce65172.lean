module

public import Erdos272.Counting.N65172.Small77Rank65172

@[expose] public section

namespace JSP233.Small77Pierce65172
open StarCompletion SmallKernel112 SparseSmall39 Small77Rank65172 Small77Kernel65172
open CrossRankBudget84364 AnchorCompletion38
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option Elab.async false

theorem pierced_cross_budget {N : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {z : ℤ} (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hPG : P⊆Ground N) (hT : T∈F) (hPc : P.card=76) (hTc : T.card=77)
    (hz : T∩P={z}) :
    ((((Avoid F {z}).filter (fun S=>¬Disjoint S P)).card : ℝ)+441750)
      ≤5700*(N : ℝ) := by
  have hzTP : z∈T∩P := by rw [hz];simp
  obtain ⟨hzT,hzP⟩ := Finset.mem_inter.mp hzTP
  have hzG := hPG hzP
  let D : Finset ℤ:={z}
  let X:=P\D
  let Y:=T\D
  let C:=(Avoid F D).filter (fun S=>¬Disjoint S P)
  have hDF : D⊆Ground N := by intro x hx;have he:=Finset.mem_singleton.mp hx;exact he.symm ▸ hzG
  have hDP : D⊆P := by intro x hx;have he:=Finset.mem_singleton.mp hx;exact he.symm ▸ hzP
  have hDT : D⊆T := by intro x hx;have he:=Finset.mem_singleton.mp hx;exact he.symm ▸ hzT
  have hDN : D.Nonempty := by exact ⟨z,by simp [D]⟩
  have hCF : C⊆F := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have havoid : ∀S∈C,Disjoint S D :=
    fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxY
    have hxTP : x∈T∩P := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hxY).1,(Finset.mem_sdiff.mp hxX).1⟩
    rw [hz] at hxTP
    exact (Finset.mem_sdiff.mp hxX).2 hxTP
  have hDX : Disjoint D X := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxX;exact (Finset.mem_sdiff.mp hxX).2 hxD
  have hDY : Disjoint D Y := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxY;exact (Finset.mem_sdiff.mp hxY).2 hxD
  have hhitX : ∀S∈C,(S∩X).Nonempty := by
    intro S hS
    have hn := (Finset.mem_filter.mp hS).2
    by_contra hnone
    apply hn
    apply Finset.disjoint_left.mpr
    intro x hxS hxP
    apply hnone
    exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_sdiff.mpr
      ⟨hxP,fun hxD=>Finset.disjoint_left.mp (havoid S hS) hxS hxD⟩⟩⟩
  have hXc : X.card=75 := by
    have hh:=Finset.card_sdiff_add_card_eq_card hDP
    change X.card+D.card=P.card at hh
    have hDc : D.card=1 := by simp [D]
    omega
  have hYc : Y.card=76 := by
    have hh:=Finset.card_sdiff_add_card_eq_card hDT
    change Y.card+D.card=T.card at hh
    have hDc : D.card=1 := by simp [D]
    omega
  have hDc : D.card=1 := by simp [D]
  have hb := actual_cross_hit_budget (legal_sub hlegal hCF) (fun S hS=>hbad S (hCF hS))
    hDF (Finset.sdiff_subset.trans hPG) (Finset.sdiff_subset.trans (hlegal.1 T hT))
    hXY hDX hDY havoid hhitX
    (fun S hS=>hits_diff hlegal hT (hCF hS) hDT hDN (havoid S hS))
  have hr : (C.card : ℝ)+(X.card : ℝ)*Y.card*(D.card+2)+
      (Y.card : ℝ)*(X.card.choose 2 : ℝ)+(X.card : ℝ)*(Y.card.choose 2 : ℝ)
      ≤(X.card : ℝ)*Y.card*(Ground N).card := by exact_mod_cast hb
  rw [hXc,hYc,hDc,ground_card] at hr
  norm_num [Nat.choose_two_right] at hr
  linarith only [hr]

theorem outside_budget {N : ℕ} {F : Finset (Finset ℤ)} {A B : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hA : A∈F) (hB : B∈F) (hne : A≠B)
    (hAc : A.card=77) (hBc : B.card=77) (hAB : (A∩B).card=76) :
    (Avoid F (A∩B)).card≤N := by
  let P:=A∩B
  let O:=Avoid F P
  change O.card≤N
  have hOF : O⊆F := Finset.filter_subset _ _
  have hPN : P.Nonempty := Finset.card_pos.mp (by change 0<(A∩B).card;omega)
  obtain ⟨a,haP,hArep⟩ := one_extra (A:=A) (P:=P) Finset.inter_subset_left hAc hAB
  obtain ⟨b,hbP,hBrep⟩ := one_extra (A:=B) (P:=P) Finset.inter_subset_right hBc hAB
  have hab : a≠b := by intro he;exact hne (hArep.trans (he ▸ hBrep.symm))
  by_cases ho : O.Nonempty
  · have hp : ∀S∈O,a∈S ∧ b∈S := by
      intro S hS
      exact outside_petals hlegal hA hB (hOF hS) hPN hArep hBrep (Finset.mem_filter.mp hS).2
    have hc := actual_two_point_crooked_ground_capacity (Ground N) O a b hab ho
      (legal_sub hlegal hOF) (fun S hS=>hbad S (hOF hS))
      (fun S hS=>(hp S hS).1) (fun S hS=>(hp S hS).2)
    rw [ground_card] at hc;omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp ho
    simp only [he,Finset.card_empty,Nat.zero_le]

theorem pierced_cover (F : Finset (Finset ℤ)) (P : Finset ℤ) (z : ℤ) :
    F.card≤(RootPart F z).card+
      ((Avoid F {z}).filter (fun S=>¬Disjoint S P)).card+(Avoid F P).card := by
  let C:=(Avoid F {z}).filter (fun S=>¬Disjoint S P)
  let O:=Avoid F P
  change F.card≤(RootPart F z).card+C.card+O.card
  have hcover : F⊆RootPart F z ∪ (C∪O) := by
    intro S hS
    by_cases hzS : z∈S
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hS,hzS⟩))
    · apply Finset.mem_union.mpr;right
      by_cases hd : Disjoint S P
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hS,hd⟩))
      · apply Finset.mem_union.mpr;left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hS,?_⟩,hd⟩
        apply Finset.disjoint_left.mpr
        intro x hxS hxD
        exact hzS ((Finset.mem_singleton.mp hxD) ▸ hxS)
  have hh:=(Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hl:=Finset.card_union_le C O
  omega

theorem pierced_sharp_credit {N : ℕ} {F : Finset (Finset ℤ)} {A B T : Finset ℤ}
    (hN : 78≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅)
    (hA : A∈F) (hB : B∈F) (hT : T∈F) (hne : A≠B)
    (hAc : A.card=77) (hBc : B.card=77) (hTc : T.card=77)
    (hAB : (A∩B).card=76) (hTP : (T∩(A∩B)).card=1) :
    (F.card : ℝ)≤5778*(N : ℝ)-444830 := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hTP
  have hzG : z∈Ground N := hlegal.1 A hA
    (Finset.mem_inter.mp (Finset.mem_inter.mp
      (show z∈T∩(A∩B) by rw [hz];simp)).2).1
  have hc := pierced_cross_budget hlegal hbad
    (Finset.inter_subset_left.trans (hlegal.1 A hA)) hT hAB hTc hz
  have hoR : ((Avoid F (A∩B)).card : ℝ)≤N := by
    exact_mod_cast outside_budget hlegal hbad hA hB hne hAc hBc hAB
  have hpR : (F.card : ℝ)≤(RootPart F z).card+
      ((Avoid F {z}).filter (fun S=>¬Disjoint S (A∩B))).card+(Avoid F (A∩B)).card := by
    exact_mod_cast pierced_cover F (A∩B) z
  have hr:=root_budget hN hlegal hbad hkernel hzG
  linarith only [hpR,hoR,hr,hc]

theorem pierced_credit {N : ℕ} {F : Finset (Finset ℤ)} {A B T : Finset ℤ}
    (hN : 78≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅)
    (hA : A∈F) (hB : B∈F) (hT : T∈F) (hne : A≠B)
    (hAc : A.card=77) (hBc : B.card=77) (hTc : T.card=77)
    (hAB : (A∩B).card=76) (hTP : (T∩(A∩B)).card=1) :
    (F.card : ℝ)≤5779*(N : ℝ)-231312 := by
  have hb := pierced_sharp_credit hN hlegal hbad hkernel hA hB hT hne hAc hBc hTc hAB hTP
  linarith only [hb,Nat.cast_nonneg (α:=ℝ) N]

#print axioms pierced_cross_budget
#print axioms outside_budget
#print axioms pierced_cover
#print axioms pierced_sharp_credit
#print axioms pierced_credit
end
end JSP233.Small77Pierce65172
