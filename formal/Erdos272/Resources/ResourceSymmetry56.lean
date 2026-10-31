import Erdos272.Arithmetic.CoprimeDensity52

namespace JSP233.ResourceSymmetry56
open MiddleJoint51 CoprimeDensity52
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

theorem mem_box {A B C D : ℕ} {p : ℕ×ℕ} :
    p∈CoprimeBox A B C D ↔ A<p.1 ∧ p.1≤B ∧ C<p.2 ∧ p.2≤D ∧ p.1.Coprime p.2 := by
  simp [CoprimeBox,Finset.mem_product,and_assoc]

theorem mem_triangle {e M : ℕ} {p : ℕ×ℕ} :
    p∈UpperTriangle e M ↔ e<p.1 ∧ p.1≤M ∧ e<p.2 ∧ p.2≤M ∧
      p.1.Coprime p.2 ∧ p.1<p.2 := by
  simp [UpperTriangle,mem_box,and_assoc]

theorem mem_rectangle {A B : ℕ} {p : ℕ×ℕ} :
    p∈coprimeRectangle A B ↔ 0<p.1 ∧ p.1≤A ∧ 0<p.2 ∧ p.2≤B ∧ p.1.Coprime p.2 := by
  simp only [coprimeRectangle,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  omega

theorem mem_swapped_triangle {M : ℕ} {p : ℕ×ℕ} :
    p∈(UpperTriangle 0 M).image Prod.swap ↔
      0<p.1 ∧ p.1≤M ∧ 0<p.2 ∧ p.2≤M ∧ p.1.Coprime p.2 ∧ p.2<p.1 := by
  constructor
  · rintro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1,hM1,h2,hM2,hcop,hlt⟩ := mem_triangle.mp hq
    exact ⟨h2,hM2,h1,hM1,hcop.symm,hlt⟩
  · rintro ⟨h1,hM1,h2,hM2,hcop,hlt⟩
    exact Finset.mem_image.mpr ⟨p.swap,mem_triangle.mpr ⟨h2,hM2,h1,hM1,hcop.symm,hlt⟩,Prod.swap_swap p⟩

theorem actual_coprime_diagonal (M : ℕ) :
    ((coprimeRectangle M M).filter (fun p=>p.1=p.2)).card=(if 0<M then 1 else 0) := by
  by_cases hM : 0<M
  · have he : (coprimeRectangle M M).filter (fun p=>p.1=p.2)={(1,1)} := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp,hdiag⟩ := Finset.mem_filter.mp hp
        obtain ⟨_h1,_hM1,_h2,_hM2,hcop⟩ := mem_rectangle.mp hp
        have hone : p.1=1 := by simpa only [←hdiag,Nat.Coprime,Nat.gcd_self] using hcop
        have hp1 : p=(1,1) := Prod.ext hone (by omega)
        exact Finset.mem_singleton.mpr hp1
      · intro hp
        have hp1 := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_filter.mpr ⟨mem_rectangle.mpr ⟨by omega,by omega,by omega,by omega,by decide⟩,rfl⟩
    rw [he,Finset.card_singleton,if_pos hM]
  · have hz : M=0 := by omega
    subst M
    simp [coprimeRectangle]

theorem actual_square_symmetry (M : ℕ) :
    2*(UpperTriangle 0 M).card+(if 0<M then 1 else 0)=(coprimeRectangle M M).card := by
  let U:=UpperTriangle 0 M
  let V:=U.image Prod.swap
  let D:=(coprimeRectangle M M).filter (fun p=>p.1=p.2)
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hl := (mem_triangle.mp hp).2.2.2.2.2
    have hr := (mem_swapped_triangle.mp hq).2.2.2.2.2
    omega
  have hD : Disjoint (U∪V) D := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have he := (Finset.mem_filter.mp hq).2
    rcases Finset.mem_union.mp hp with hp|hp
    · have hl := (mem_triangle.mp hp).2.2.2.2.2
      omega
    · have hl := (mem_swapped_triangle.mp hp).2.2.2.2.2
      omega
  have hfull : coprimeRectangle M M=U∪V∪D := by
    ext p
    constructor
    · intro hp
      obtain ⟨h1,hM1,h2,hM2,hcop⟩ := mem_rectangle.mp hp
      rcases lt_trichotomy p.1 p.2 with hl|he|hr
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_triangle.mpr ⟨h1,hM1,h2,hM2,hcop,hl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,he⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_swapped_triangle.mpr ⟨h1,hM1,h2,hM2,hcop,hr⟩))
    · intro hp
      rcases Finset.mem_union.mp hp with hp|hp
      · rcases Finset.mem_union.mp hp with hp|hp
        · obtain ⟨h1,hM1,h2,hM2,hcop,_hlt⟩ := mem_triangle.mp hp
          exact mem_rectangle.mpr ⟨h1,hM1,h2,hM2,hcop⟩
        · obtain ⟨h1,hM1,h2,hM2,hcop,_hlt⟩ := mem_swapped_triangle.mp hp
          exact mem_rectangle.mpr ⟨h1,hM1,h2,hM2,hcop⟩
      · exact (Finset.mem_filter.mp hp).1
  have hv : V.card=U.card := Finset.card_image_of_injective _ Prod.swap_injective
  have hd : D.card=(if 0<M then 1 else 0) := actual_coprime_diagonal M
  have hc := congrArg Finset.card hfull
  rw [Finset.card_union_of_disjoint hD,Finset.card_union_of_disjoint hUV,hv,hd] at hc
  dsimp only [U] at hc
  omega

theorem actual_upper_split {e M : ℕ} (heM : e≤M) :
    (UpperTriangle 0 e).card+(CoprimeBox 0 e e M).card+(UpperTriangle e M).card=
      (UpperTriangle 0 M).card := by
  let T:=UpperTriangle 0 M
  have hlow : T.filter (fun p=>p.2≤e)=UpperTriangle 0 e := by
    ext p
    simp only [T,Finset.mem_filter,mem_triangle]
    omega
  let V:=T.filter (fun p=>¬p.2≤e)
  have hbox : V.filter (fun p=>p.1≤e)=CoprimeBox 0 e e M := by
    ext p
    simp only [V,T,Finset.mem_filter,mem_triangle,mem_box]
    omega
  have htri : V.filter (fun p=>¬p.1≤e)=UpperTriangle e M := by
    ext p
    simp only [V,T,Finset.mem_filter,mem_triangle]
    omega
  have h1 := Finset.card_filter_add_card_filter_not (s:=T) (fun p=>p.2≤e)
  have h2 := Finset.card_filter_add_card_filter_not (s:=V) (fun p=>p.1≤e)
  rw [hlow] at h1
  rw [hbox,htri] at h2
  change (UpperTriangle 0 e).card+V.card=T.card at h1
  dsimp only [T] at h1
  omega

theorem actual_square_tail_identity {e M : ℕ} (heM : e≤M) :
    2*((CoprimeBox 0 e e M).card+(UpperTriangle e M).card)+
      (coprimeRectangle e e).card+(if e=0 ∧ 0<M then 1 else 0)=
        (coprimeRectangle M M).card := by
  have hM := actual_square_symmetry M
  have he := actual_square_symmetry e
  have hp := actual_upper_split heM
  have hdelta : (if 0<e then 1 else 0)+(if e=0 ∧ 0<M then 1 else 0)=(if 0<M then 1 else 0) := by
    by_cases he0 : e=0
    · subst e
      simp
    · have hepos : 0<e := by omega
      have hMpos : 0<M := by omega
      simp only [if_pos hepos,if_pos hMpos,he0,false_and,if_false]
  omega

#print axioms mem_box
#print axioms mem_triangle
#print axioms mem_rectangle
#print axioms mem_swapped_triangle
#print axioms actual_coprime_diagonal
#print axioms actual_square_symmetry
#print axioms actual_upper_split
#print axioms actual_square_tail_identity
end
end JSP233.ResourceSymmetry56
