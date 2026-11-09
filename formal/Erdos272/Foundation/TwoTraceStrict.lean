module

public import Erdos272.Foundation.TwoTrace

@[expose] public section

/-!
Simultaneous saturation of the two genuine exterior-point groups is
incompatible with AP legality between the groups. This improves the
two-trace geometric estimate by one integer unit.
-/

namespace JSP233.TwoTraceStrict

open StarCompletion PrivateFinset TwoTrace

/-- When the actual group cardinality equals the actual tail cardinality,
the proved private assignment covers the tail. Consequently every member
has exactly one exterior point; this property is derived, not assumed. -/
theorem saturated_group_single_exterior
    (Ω I : Finset Int) (D : Finset (Finset Int)) (d a : Int)
    (haI : a ∈ I) (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S) (haD : ∀ S ∈ D, a ∈ S)
    (hcore : ∀ S ∈ D, PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ I))
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ T))
    (hsat : D.card = (Ω \ I).card) :
    ∀ x ∈ Ω \ I, ∃ S ∈ D, x ∈ S ∧
      ∀ y ∈ S, y ∉ I → y = x := by
  classical
  let e := D.equivFin.symm
  let A : Fin D.card → Int → Prop := fun i x => x ∈ (e i).val
  have hcrookedA : ∀ i, ¬ PrivateUnion.IsAP (A i) := by
    intro i hi
    exact hcrooked _ (e i).property ((isAP_iff_predicate _).mpr hi)
  have hpA : ∀ i, A i a := fun i => haD _ (e i).property
  have hcoreA : ∀ i, PrivateUnion.APAt d a (fun x => A i x ∧ x ∈ I) :=
    fun i => hcore _ (e i).property
  have hpairA : ∀ i j, i ≠ j →
      PrivateUnion.APAt d a (fun x => A i x ∧ A j x) := by
    intro i j hij
    apply hpair _ (e i).property _ (e j).property
    intro he
    apply hij
    exact e.injective (Subtype.ext he)
  rcases PrivateUnion.private_selection d a A (fun x => x ∈ I)
    hcrookedA haI hpA hcoreA hpairA with ⟨f,hf,hpriv,hinj⟩
  let R := Finset.univ.image f
  have hRsub : R ⊆ Ω \ I := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i,_,rfl⟩
    exact Finset.mem_sdiff.mpr
      ⟨hground _ (e i).property (hf i).1,(hf i).2⟩
  have hRcard : R.card = D.card := by
    change (Finset.univ.image f).card = D.card
    rw [Finset.card_image_of_injective _ (fun i j h => hinj i j h)]
    simp
  have hR : R = Ω \ I := by
    apply Finset.eq_of_subset_of_card_le hRsub
    omega
  intro x hx
  have hxR : x ∈ R := hR.symm ▸ hx
  rcases Finset.mem_image.mp hxR with ⟨i,_,hix⟩
  refine ⟨(e i).val,(e i).property,?_,?_⟩
  · simpa only [← hix] using (hf i).1
  · intro y hy hyI
    have hyE : y ∈ Ω \ I := Finset.mem_sdiff.mpr
      ⟨hground _ (e i).property hy,hyI⟩
    have hyR : y ∈ R := hR.symm ▸ hyE
    rcases Finset.mem_image.mp hyR with ⟨j,_,hjy⟩
    have hji : j = i := by
      by_contra hne
      apply hpriv j i hne
      simpa only [hjy] using hy
    subst j
    exact hjy.symm.trans hix

theorem fine_group_facts
    (Ω : Finset Int) (D : Finset (Finset Int)) (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    (D.filter (fun S => Hull a t ⊆ S)).card ≤ (Ω \ Hull a t).card ∧
    ((D.filter (fun S => Hull a t ⊆ S)).card = (Ω \ Hull a t).card →
      ∀ x ∈ Ω \ Hull a t, ∃ S ∈ D, Hull a t ⊆ S ∧ x ∈ S ∧
        ∀ y ∈ S, y ∉ Hull a t → y = x) := by
  classical
  let Fine := D.filter (fun S => Hull a t ⊆ S)
  have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
  have hgr : ∀ S ∈ Fine, S ⊆ Ω := by
    intro S hS
    exact hground S (Finset.mem_filter.mp hS).1
  have hcr : ∀ S ∈ Fine, ¬ IsAP S := by
    intro S hS
    exact hcrooked S (Finset.mem_filter.mp hS).1
  have haF : ∀ S ∈ Fine, a ∈ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2 haI
  have hcore : ∀ S ∈ Fine,
      PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ Hull a t) := by
    intro S hS
    apply PrivateUnion.APAt_congr 1 a _ _ (hull_APAt a t)
    intro x
    exact ⟨fun hx => ⟨(Finset.mem_filter.mp hS).2 hx,hx⟩,fun hx => hx.2⟩
  have hp : ∀ S ∈ Fine, ∀ T ∈ Fine, S ≠ T →
      PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
    intro S hS T hT hne
    have hSf := Finset.mem_filter.mp hS
    have hTf := Finset.mem_filter.mp hT
    exact fine_pair_step_one a t ht S T hSf.2 hTf.2
      (hpair S hSf.1 T hTf.1 hne)
  refine ⟨group_le_tail Ω (Hull a t) Fine 1 a haI hgr hcr haF hcore hp,?_⟩
  intro hsat x hx
  rcases saturated_group_single_exterior Ω (Hull a t) Fine 1 a haI
    hgr hcr haF hcore hp hsat x hx with ⟨S,hS,hxS,huniq⟩
  exact ⟨S,(Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2,hxS,huniq⟩

theorem coarse_group_facts
    (Ω : Finset Int) (D : Finset (Finset Int)) (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    (D.filter (fun S => ¬ Hull a t ⊆ S)).card ≤ (Ω \ Hull a t).card ∧
    ((D.filter (fun S => ¬ Hull a t ⊆ S)).card = (Ω \ Hull a t).card →
      ∀ x ∈ Ω \ Hull a t, ∃ S ∈ D, (¬ Hull a t ⊆ S) ∧ x ∈ S ∧
        ∀ y ∈ S, y ∉ Hull a t → y = x) := by
  classical
  let Coarse := D.filter (fun S => ¬ Hull a t ⊆ S)
  have htr := family_two_traces a t ht D hK hf hpair
  have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
  have hgr : ∀ S ∈ Coarse, S ⊆ Ω := by
    intro S hS
    exact hground S (Finset.mem_filter.mp hS).1
  have hcr : ∀ S ∈ Coarse, ¬ IsAP S := by
    intro S hS
    exact hcrooked S (Finset.mem_filter.mp hS).1
  have haF : ∀ S ∈ Coarse, a ∈ S := by
    intro S hS
    exact hK S (Finset.mem_filter.mp hS).1 (left_mem_anchor a t)
  have hcore : ∀ S ∈ Coarse,
      PrivateUnion.APAt 2 a (fun x => x ∈ S ∧ x ∈ Hull a t) := by
    intro S hS
    have hSf := Finset.mem_filter.mp hS
    have he : S ∩ Hull a t = Anchor a t := (htr S hSf.1).resolve_left hSf.2
    apply PrivateUnion.APAt_congr 2 a _ _ (anchor_APAt a t)
    intro x
    rw [← he]
    exact Finset.mem_inter
  have hp : ∀ S ∈ Coarse, ∀ T ∈ Coarse, S ≠ T →
      PrivateUnion.APAt 2 a (fun x => x ∈ S ∧ x ∈ T) := by
    intro S hS T hT hne
    have hSf := Finset.mem_filter.mp hS
    have hTf := Finset.mem_filter.mp hT
    exact nonfine_pair_step_two a t ht S T (hK S hSf.1) (hK T hTf.1)
      hSf.2 (hpair S hSf.1 T hTf.1 hne)
  refine ⟨group_le_tail Ω (Hull a t) Coarse 2 a haI hgr hcr haF hcore hp,?_⟩
  intro hsat x hx
  rcases saturated_group_single_exterior Ω (Hull a t) Coarse 2 a haI
    hgr hcr haF hcore hp hsat x hx with ⟨S,hS,hxS,huniq⟩
  exact ⟨S,(Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2,hxS,huniq⟩

/-- Both groups cannot saturate the same tail: matching one exterior point
in both groups makes the crooked coarse member a subset of a fine member,
contradicting the actual AP intersection condition. -/
theorem two_groups_strict_tail_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + 1 ≤ 2 * (Ω \ Hull a t).card := by
  classical
  have hfacts := fine_group_facts Ω D a t ht hground hcrooked hpair
  have hcfacts := coarse_group_facts Ω D a t ht hground hcrooked hK hf hpair
  have hpartition := Finset.card_filter_add_card_filter_not (s := D)
    (fun S => Hull a t ⊆ S)
  by_contra hn
  have hfsat : (D.filter (fun S => Hull a t ⊆ S)).card =
      (Ω \ Hull a t).card := by omega
  have hcsat : (D.filter (fun S => ¬ Hull a t ⊆ S)).card =
      (Ω \ Hull a t).card := by omega
  have hpos : 0 < (Ω \ Hull a t).card := by
    rcases hf with ⟨S,hS,hSI⟩
    have hfm : S ∈ D.filter (fun S => Hull a t ⊆ S) :=
      Finset.mem_filter.mpr ⟨hS,hSI⟩
    have hfp := Finset.card_pos.mpr ⟨S,hfm⟩
    omega
  rcases Finset.card_pos.mp hpos with ⟨x,hx⟩
  rcases hfacts.2 hfsat x hx with ⟨S,hS,hSI,hxS,_⟩
  rcases hcfacts.2 hcsat x hx with ⟨T,hT,hTI,hxT,hTuniq⟩
  have hTS : T ⊆ S := by
    intro y hyT
    by_cases hyI : y ∈ Hull a t
    · exact hSI hyI
    · rw [hTuniq y hyT hyI]
      exact hxS
  have hne : S ≠ T := by
    intro he
    exact hTI (he ▸ hSI)
  have he : S ∩ T = T := Finset.inter_eq_right.mpr hTS
  have hAP := hpair S hS T hT hne
  rw [he] at hAP
  exact hcrooked T hT hAP

/-- Excluding a real ground root and evaluating the actual hull cardinality
turns the strict tail estimate into `h + 4 k + 1 <= 2 N`. -/
theorem fine_anchor_strict_linear_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + 4 * (Anchor a t).card + 1 ≤ 2 * Ω.card := by
  have hgr : ∀ S ∈ D, S ⊆ Ω.erase c := by
    intro S hS x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact havoid S hS (he ▸ hx),hground S hS hx⟩
  have htail := two_groups_strict_tail_bound (Ω.erase c) D a t ht
    hgr hcrooked hK hf hpair
  rcases hf with ⟨S,hS,hfS⟩
  have hcI : c ∉ Hull a t := by
    intro hcin
    exact havoid S hS (hfS hcin)
  have hI : Hull a t ⊆ Ω.erase c := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact hcI (he ▸ hx),hground S hS (hfS hx)⟩
  have hslots := Finset.card_sdiff_add_card_eq_card hI
  have hΩpos : 0 < Ω.card := Finset.card_pos.mpr ⟨c,hc⟩
  rw [Finset.card_erase_of_mem hc] at hslots
  have hsize := hull_anchor_card a t
  omega

/-- The actual step-two kernel payment now includes the additional boundary
`N = 3 k + 1`, which was not covered by the nonstrict two-group estimate. -/
theorem large_actual_kernel_plus_one_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hkernel : Kernel Ω D = Anchor a t)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hlarge : Ω.card ≤ 3 * (Kernel Ω D).card + 1) :
    D.card + (Kernel Ω D).card ≤ Ω.card := by
  classical
  have hK : ∀ S ∈ D, Anchor a t ⊆ S := by
    intro S hS x hx
    rw [← hkernel] at hx
    exact (Finset.mem_filter.mp hx).2 S hS
  by_cases hf : ∃ S ∈ D, Hull a t ⊆ S
  · have hlinear := fine_anchor_strict_linear_bound Ω D c a t ht hc
      hground havoid hcrooked hK hf hpair
    rw [hkernel] at hlarge ⊢
    omega
  · have hnf : ∀ S ∈ D, ¬ Hull a t ⊆ S := by
      intro S hS hfull
      exact hf ⟨S,hS,hfull⟩
    have hp : ∀ S ∈ D, a ∈ S := fun S hS => hK S hS (left_mem_anchor a t)
    exact same_step_card_bound Ω D 2 a hm hground hcrooked hp
      (no_fine_same_step a t ht D hK hnf hpair)

/-- The original extremal counterexample, conditional only on the explicit
starred bound, must satisfy the stricter step-two kernel constraint. -/
theorem counterexample_step_two_strict_constraints
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a : Int) (t B : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hkernel : Kernel Ω (Avoiders F c) = Anchor a t)
    (hover : B < F.card) :
    (∃ S ∈ Avoiders F c, Hull a t ⊆ S) ∧
    (Avoiders F c).card + 4 * (CommonKernel Ω F c).card + 1 ≤ 2 * Ω.card ∧
    3 * (CommonKernel Ω F c).card + 2 ≤ Ω.card := by
  have hprev := counterexample_step_two_constraints Ω F c a t B ht hc
    hF hstar hm hcrooked hkernel hover
  have hf := hprev.1
  have hground : ∀ S ∈ Avoiders F c, S ⊆ Ω := by
    intro S hS
    exact hF.1 S (Finset.mem_filter.mp hS).1
  have havoid : ∀ S ∈ Avoiders F c, c ∉ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hK : ∀ S ∈ Avoiders F c, Anchor a t ⊆ S := by
    intro S hS x hx
    rw [← hkernel] at hx
    exact (Finset.mem_filter.mp hx).2 S hS
  have hpair : ∀ S ∈ Avoiders F c, ∀ T ∈ Avoiders F c,
      S ≠ T → IsAP (S ∩ T) := by
    intro S hS T hT hne
    exact hF.2 S (Finset.mem_filter.mp hS).1 T
      (Finset.mem_filter.mp hT).1 hne
  have hlinear := fine_anchor_strict_linear_bound Ω (Avoiders F c) c a t ht hc
    hground havoid hcrooked hK hf hpair
  have hk : CommonKernel Ω F c = Anchor a t := hkernel
  have hlinear' : (Avoiders F c).card +
      4 * (CommonKernel Ω F c).card + 1 ≤ 2 * Ω.card := by
    rw [hk]
    exact hlinear
  have hdeficit := counterexample_forces_kernel_deficit Ω F c B hc hF hstar hover
  exact ⟨hf,hlinear',by omega⟩

#print axioms saturated_group_single_exterior
#print axioms fine_group_facts
#print axioms coarse_group_facts
#print axioms two_groups_strict_tail_bound
#print axioms fine_anchor_strict_linear_bound
#print axioms large_actual_kernel_plus_one_bound
#print axioms counterexample_step_two_strict_constraints

end JSP233.TwoTraceStrict
