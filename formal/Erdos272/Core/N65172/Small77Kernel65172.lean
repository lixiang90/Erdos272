module

public import Erdos272.Core.N65172.APCoatom65172
public import Erdos272.Core.SmallKernel112

@[expose] public section

namespace JSP233.Small77Kernel65172
open StarCompletion SmallKernel112 SparseSmall39
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem inter_le {A B : Finset ℤ} (hA : A.card=77) (hB : B.card=77)
    (hne : A≠B) : (A∩B).card≤76 := by
  have hle := Finset.card_le_card (Finset.inter_subset_left (s₁:=A) (s₂:=B))
  by_contra hn
  have hIA : A∩B=A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hAB : A⊆B := by rw [←hIA]; exact Finset.inter_subset_right
  exact hne (Finset.eq_of_subset_of_card_le hAB (by omega))

theorem one_extra {A P : Finset ℤ} (hPA : P⊆A) (hA : A.card=77) (hP : P.card=76) :
    ∃ a : ℤ, a∉P ∧ A=P∪{a} := by
  have hc := Finset.card_sdiff_add_card_eq_card hPA
  have hone : (A\P).card=1 := by omega
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
  have haA : a∈A\P := by rw [ha]; simp
  refine ⟨a,(Finset.mem_sdiff.mp haA).2,?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxP : x∈P
    · exact Finset.mem_union.mpr (Or.inl hxP)
    · have hh : x∈A\P := Finset.mem_sdiff.mpr ⟨hx,hxP⟩
      rw [ha] at hh
      exact Finset.mem_union.mpr (Or.inr hh)
  · intro hx
    rcases Finset.mem_union.mp hx with hxP | hxA
    · exact hPA hxP
    · have he := Finset.mem_singleton.mp hxA
      exact he.symm ▸ (Finset.mem_sdiff.mp haA).1

theorem core_or_disjoint {Ω : Finset ℤ} {H : Finset (Finset ℤ)}
    (hlegal : Legal Ω H) (hbad : ∀S∈H,¬IsAP S) (hcard : ∀S∈H,S.card=77)
    (hlarge : ∀ A∈H,∀ B∈H,A≠B→2≤(A∩B).card→(A∩B).card=76)
    (hnoone : ∀ A∈H,∀ B∈H,A≠B→(A∩B).card=76→∀T∈H,(T∩(A∩B)).card≠1)
    {A B S : Finset ℤ} (hA : A∈H) (hB : B∈H) (hne : A≠B)
    (hAB : (A∩B).card=76) (hS : S∈H) :
    A∩B⊆S ∨ Disjoint S (A∩B) := by
  by_cases htwo : 2≤(S∩(A∩B)).card
  · left
    by_cases he : A=S
    · rw [←he]; exact Finset.inter_subset_left
    have hsub : S∩(A∩B)⊆A∩S := by
      intro x hx
      obtain ⟨hxS,hxAB⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxAB).1,hxS⟩
    have hc : (A∩S).card=76 := hlarge A hA S hS he (htwo.trans (Finset.card_le_card hsub))
    have heq : A∩B=A∩S := APCoatom65172.unique_AP_coatom (m:=76)
      (by decide) (by simpa only [hcard A hA]) (hbad A hA)
      Finset.inter_subset_left Finset.inter_subset_left hAB hc
      (hlegal.2 A hA B hB hne) (hlegal.2 A hA S hS he)
    rw [heq];exact Finset.inter_subset_right
  · right
    have hnot := hnoone A hA B hB hne hAB S hS
    have hz : (S∩(A∩B)).card=0 := by omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)

theorem outside_petals {Ω A B P T : Finset ℤ} {H : Finset (Finset ℤ)} {a b : ℤ}
    (hlegal : Legal Ω H) (hA : A∈H) (hB : B∈H) (hT : T∈H)
    (hP : P.Nonempty) (hArep : A=P∪{a}) (hBrep : B=P∪{b})
    (hdis : Disjoint T P) : a∈T ∧ b∈T := by
  have hneA : T≠A := by
    intro he
    obtain ⟨x,hx⟩ := hP
    exact Finset.disjoint_left.mp hdis (he.symm ▸ (hArep.symm ▸ Finset.mem_union.mpr (Or.inl hx))) hx
  have hneB : T≠B := by
    intro he
    obtain ⟨x,hx⟩ := hP
    exact Finset.disjoint_left.mp hdis (he.symm ▸ (hBrep.symm ▸ Finset.mem_union.mpr (Or.inl hx))) hx
  constructor
  · obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 T hT A hA hneA)
    obtain ⟨hxT,hxA⟩ := Finset.mem_inter.mp hx
    rw [hArep] at hxA
    rcases Finset.mem_union.mp hxA with hxP | hxa
    · exact (Finset.disjoint_left.mp hdis hxT hxP).elim
    · exact (Finset.mem_singleton.mp hxa) ▸ hxT
  · obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 T hT B hB hneB)
    obtain ⟨hxT,hxB⟩ := Finset.mem_inter.mp hx
    rw [hBrep] at hxB
    rcases Finset.mem_union.mp hxB with hxP | hxb
    · exact (Finset.disjoint_left.mp hdis hxT hxP).elim
    · exact (Finset.mem_singleton.mp hxb) ▸ hxT

theorem fixed_core_card {N : ℕ} {H : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) H) (hbad : ∀S∈H,¬IsAP S) (hcard : ∀S∈H,S.card=77)
    (hkernel : PrivateFinset.Kernel (Ground N) H=∅)
    (hlarge : ∀ A∈H,∀ B∈H,A≠B→2≤(A∩B).card→(A∩B).card=76)
    (hnoone : ∀ A∈H,∀ B∈H,A≠B→(A∩B).card=76→∀T∈H,(T∩(A∩B)).card≠1)
    {A B : Finset ℤ} (hA : A∈H) (hB : B∈H) (hne : A≠B)
    (hAB : (A∩B).card=76) : H.card≤78 := by
  let P:=A∩B
  have hPc : P.card=76 := hAB
  have hPN : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,haP,hArep⟩ := one_extra (A:=A) (P:=P) Finset.inter_subset_left (hcard A hA) hPc
  obtain ⟨b,hbP,hBrep⟩ := one_extra (A:=B) (P:=P) Finset.inter_subset_right (hcard B hB) hPc
  have hab : a≠b := by intro he;exact hne (hArep.trans (he ▸ hBrep.symm))
  obtain ⟨x,hxP⟩ := Finset.card_pos.mp (show 0<P.card by omega)
  obtain ⟨T,hT,hxT⟩ := actual_omitter_of_empty_kernel hkernel x
    (hlegal.1 A hA (Finset.mem_inter.mp hxP).1)
  have hTP : Disjoint T P := by
    rcases core_or_disjoint hlegal hbad hcard hlarge hnoone hA hB hne hAB hT with hsub | hd
    · exact (hxT (hsub hxP)).elim
    · exact hd
  have ht := outside_petals hlegal hA hB hT hPN hArep hBrep hTP
  have unique : ∀U∈H,Disjoint U P→U=T := by
    intro U hU hUP
    by_contra hUT
    have hu := outside_petals hlegal hA hB hU hPN hArep hBrep hUP
    have hpair : ({a,b}:Finset ℤ)⊆T∩U := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_inter.mpr ⟨ht.1,hu.1⟩
      · have he := Finset.mem_singleton.mp hy
        exact he.symm ▸ Finset.mem_inter.mpr ⟨ht.2,hu.2⟩
    have htwo : 2≤(T∩U).card := by simpa only [Finset.card_pair hab] using Finset.card_le_card hpair
    have hc := hlarge T hT U hU (Ne.symm hUT) htwo
    have he : A∩(T∩U)={a} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyA,hyTU⟩ := Finset.mem_inter.mp hy
        rw [hArep] at hyA
        rcases Finset.mem_union.mp hyA with hyP | hya
        · exact (Finset.disjoint_left.mp hTP (Finset.mem_inter.mp hyTU).1 hyP).elim
        · exact hya
      · intro hy
        have hyA : y=a := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_inter.mpr ⟨hArep.symm ▸ Finset.mem_union.mpr (Or.inr (by simp)),
          Finset.mem_inter.mpr ⟨ht.1,hu.1⟩⟩
    have hnot := hnoone T hT U hU (Ne.symm hUT) hc A hA
    apply hnot
    rw [he];simp
  have hcover : H⊆insert T (T.image (fun y=>P∪{y})) := by
    intro S hS
    rcases core_or_disjoint hlegal hbad hcard hlarge hnoone hA hB hne hAB hS with hPS | hd
    · obtain ⟨y,hyP,hSrep⟩ := one_extra hPS (hcard S hS) hPc
      have hneST : S≠T := by
        intro he
        exact Finset.disjoint_left.mp hTP (he ▸ hPS hxP) hxP
      obtain ⟨z,hz⟩ := isAP_nonempty (hlegal.2 S hS T hT hneST)
      obtain ⟨hzS,hzT⟩ := Finset.mem_inter.mp hz
      rw [hSrep] at hzS
      have hyT : y∈T := by
        rcases Finset.mem_union.mp hzS with hzP | hzy
        · exact (Finset.disjoint_left.mp hTP hzT hzP).elim
        · exact (Finset.mem_singleton.mp hzy) ▸ hzT
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨y,hyT,hSrep.symm⟩))
    · exact Finset.mem_insert.mpr (Or.inl (unique S hS hd))
  have hb := (Finset.card_le_card hcover).trans (Finset.card_insert_le _ _)
  have hi := Finset.card_image_le (s:=T) (f:=fun y=>P∪{y})
  have hc := hcard T hT
  omega

#print axioms inter_le
#print axioms one_extra
#print axioms core_or_disjoint
#print axioms outside_petals
#print axioms fixed_core_card
end
end JSP233.Small77Kernel65172
