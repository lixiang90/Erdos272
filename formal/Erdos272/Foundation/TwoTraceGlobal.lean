module

public import Erdos272.Foundation.TwoTrace

@[expose] public section

/-!
The coarse group has points private in the whole family. Combining those
with points private in the fine group charges both groups to one tail.
This eliminates the large-kernel premise for an actual step-two kernel.
-/

namespace JSP233.TwoTraceGlobal

open StarCompletion PrivateFinset TwoTrace

/-- Actual private-point theorem with a finite-set family as the other
members. It is proved from ordinary same-step AP union closure. -/
theorem private_exterior_finset
    (D : Finset (Finset Int)) (S I : Finset Int) (d a : Int)
    (haS : a ∈ S) (haI : a ∈ I) (haD : ∀ T ∈ D, a ∈ T)
    (hcrooked : ¬ IsAP S)
    (hcore : PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ I))
    (hpair : ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ T)) :
    ∃ x, x ∈ S ∧ x ∉ I ∧ ∀ T ∈ D, S ≠ T → x ∉ T := by
  classical
  let others := (D.erase S).toList.map (fun T => fun x => x ∈ T)
  have htraces : ∀ T ∈ others,
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ T x) ∧ T a := by
    intro U hU
    rcases List.mem_map.mp hU with ⟨T,hT,rfl⟩
    have hTerase := Finset.mem_erase.mp (Finset.mem_toList.mp hT)
    exact ⟨hpair T hTerase.2 (Ne.symm hTerase.1),haD T hTerase.2⟩
  rcases PrivateUnion.private_outside_core d a
    (fun x => x ∈ S) (fun x => x ∈ I) others
    (by intro h; exact hcrooked ((isAP_iff_predicate S).mpr h))
    ⟨haS,haI⟩ hcore htraces with ⟨x,hx,hxI,hpriv⟩
  refine ⟨x,hx,hxI,?_⟩
  intro T hT hne
  exact hpriv (fun y => y ∈ T) (List.mem_map.mpr
    ⟨T,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨Ne.symm hne,hT⟩),rfl⟩)

/-- Points private within one part, together with points private in the
entire family in the other part, form one injective assignment. The
classification predicate is arbitrary; the application below derives
these private points from actual AP geometry. -/
theorem joint_private_card_bound
    (Ω I : Finset Int) (D : Finset (Finset Int))
    (P : Finset Int → Prop) (hground : ∀ S ∈ D, S ⊆ Ω)
    (hex : ∀ S ∈ D, ∃ x, x ∈ S ∧ x ∉ I ∧
      ∀ T ∈ D, S ≠ T → (¬ P S ∨ P T) → x ∉ T) :
    D.card ≤ (Ω \ I).card := by
  classical
  have hex' : ∀ S : {S // S ∈ D}, ∃ x, x ∈ S.val ∧ x ∉ I ∧
      ∀ T ∈ D, S.val ≠ T → (¬ P S.val ∨ P T) → x ∉ T :=
    fun S => hex S.val S.property
  let f : {S // S ∈ D} → Int := fun S => Classical.choose (hex' S)
  have hf : ∀ S : {S // S ∈ D}, f S ∈ S.val ∧ f S ∉ I ∧
      ∀ T ∈ D, S.val ≠ T → (¬ P S.val ∨ P T) → f S ∉ T :=
    fun S => Classical.choose_spec (hex' S)
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    by_contra hne
    by_cases hPS : P S.val
    · by_cases hPT : P T.val
      · apply (hf S).2.2 T.val T.property hne (Or.inr hPT)
        simpa only [← he] using (hf T).1
      · apply (hf T).2.2 S.val S.property (Ne.symm hne) (Or.inl hPT)
        simpa only [he] using (hf S).1
    · apply (hf S).2.2 T.val T.property hne (Or.inl hPS)
      simpa only [← he] using (hf T).1
  have hsub : Finset.univ.image f ⊆ Ω \ I := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨S,_,rfl⟩
    exact Finset.mem_sdiff.mpr ⟨hground S.val S.property (hf S).1,(hf S).2.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simpa using hcard

/-- A coarse member has a private exterior point with respect to all of D,
since all its intersections, even with fine members, have step two. -/
theorem coarse_globally_private
    (D : Finset (Finset Int)) (S : Finset Int) (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hS : S ∈ D) (hcrooked : ¬ IsAP S)
    (hK : ∀ T ∈ D, Anchor a t ⊆ T)
    (hf : ∃ T ∈ D, Hull a t ⊆ T)
    (hpair : ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hSnf : ¬ Hull a t ⊆ S) :
    ∃ x, x ∈ S ∧ x ∉ Hull a t ∧ ∀ T ∈ D, S ≠ T → x ∉ T := by
  classical
  have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
  have haD : ∀ T ∈ D, a ∈ T :=
    fun T hT => hK T hT (left_mem_anchor a t)
  have htrace : S ∩ Hull a t = Anchor a t := by
    rcases hf with ⟨T,hT,hTf⟩
    have hne : S ≠ T := by
      intro he
      exact hSnf (he.symm ▸ hTf)
    have hstep := nonfine_pair_step_two a t ht S T (hK S hS) (hK T hT)
      hSnf (hpair T hT hne)
    have he := trace_eq_anchor_of_step_two a t (S ∩ T)
      (by simpa only [Finset.mem_inter] using hstep)
      (Finset.mem_inter.mpr ⟨haD S hS,haD T hT⟩)
      (Finset.mem_inter.mpr
        ⟨hK S hS (right_mem_anchor a t),hK T hT (right_mem_anchor a t)⟩)
    ext x
    rw [← he]
    simp only [Finset.mem_inter]
    exact ⟨fun hx => ⟨⟨hx.1,hTf hx.2⟩,hx.2⟩,
      fun hx => ⟨hx.1.1,hx.2⟩⟩
  have hcore : PrivateUnion.APAt 2 a (fun x => x ∈ S ∧ x ∈ Hull a t) := by
    apply PrivateUnion.APAt_congr 2 a _ _ (anchor_APAt a t)
    intro x
    rw [← htrace]
    exact Finset.mem_inter
  exact private_exterior_finset D S (Hull a t) 2 a (haD S hS) haI haD
    hcrooked hcore (fun T hT hne =>
      nonfine_pair_step_two a t ht S T (hK S hS) (hK T hT) hSnf
        (hpair T hT hne))

/-- The fine group's private points and the coarse group's globally private
points jointly inject into one actual tail. No factor two is lost. -/
theorem joint_tail_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card ≤ (Ω \ Hull a t).card := by
  classical
  apply joint_private_card_bound Ω (Hull a t) D (fun S => Hull a t ⊆ S) hground
  intro S hS
  by_cases hSI : Hull a t ⊆ S
  · let Fine := D.filter (fun T => Hull a t ⊆ T)
    have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
    have haF : ∀ T ∈ Fine, a ∈ T := by
      intro T hT
      exact (Finset.mem_filter.mp hT).2 haI
    have hcore : PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ Hull a t) := by
      apply PrivateUnion.APAt_congr 1 a _ _ (hull_APAt a t)
      intro x
      exact ⟨fun hx => ⟨hSI hx,hx⟩,fun hx => hx.2⟩
    have hp : ∀ T ∈ Fine, S ≠ T →
        PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
      intro T hT hne
      have hTf := Finset.mem_filter.mp hT
      exact fine_pair_step_one a t ht S T hSI hTf.2 (hpair S hS T hTf.1 hne)
    rcases private_exterior_finset Fine S (Hull a t) 1 a (hSI haI) haI haF
      (hcrooked S hS) hcore hp with ⟨x,hx,hxI,hpriv⟩
    refine ⟨x,hx,hxI,?_⟩
    intro T hT hne hclass
    have hTI := hclass.resolve_left (not_not.mpr hSI)
    exact hpriv T (Finset.mem_filter.mpr ⟨hT,hTI⟩) hne
  · rcases coarse_globally_private D S a t ht hS (hcrooked S hS) hK hf
      (hpair S hS) hSI with ⟨x,hx,hxI,hpriv⟩
    exact ⟨x,hx,hxI,fun T hT hne _ => hpriv T hT hne⟩

/-- A real root removes one slot, and the hull has size `2 k - 1`.
The joint assignment therefore proves `h + 2 k <= N` in the fine branch. -/
theorem fine_anchor_global_linear_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + 2 * (Anchor a t).card ≤ Ω.card := by
  have hgr : ∀ S ∈ D, S ⊆ Ω.erase c := by
    intro S hS x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact havoid S hS (he ▸ hx),hground S hS hx⟩
  have htail := joint_tail_bound (Ω.erase c) D a t ht hgr hcrooked hK hf hpair
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

/-- Every actual step-two common kernel with at least two points gives
strict payment, with no large-kernel or omitted-family-size threshold. -/
theorem step_two_actual_kernel_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hkernel : Kernel Ω D = Anchor a t)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  classical
  have hK : ∀ S ∈ D, Anchor a t ⊆ S := by
    intro S hS x hx
    rw [← hkernel] at hx
    exact (Finset.mem_filter.mp hx).2 S hS
  by_cases hf : ∃ S ∈ D, Hull a t ⊆ S
  · have hlinear := fine_anchor_global_linear_bound Ω D c a t ht hc
      hground havoid hcrooked hK hf hpair
    rw [hkernel]
    have hk := anchor_card a t
    omega
  · have hnf : ∀ S ∈ D, ¬ Hull a t ⊆ S := by
      intro S hS hfull
      exact hf ⟨S,hS,hfull⟩
    have hp : ∀ S ∈ D, a ∈ S := fun S hS => hK S hS (left_mem_anchor a t)
    exact same_step_avoiders_card_bound Ω D c 2 a hc hm hground havoid
      hcrooked hp (no_fine_same_step a t ht D hK hnf hpair)

/-- The geometric class is connected to the original legal family. Yang's
starred bound remains the only unproved extremal premise, explicitly named. -/
theorem step_two_avoiders_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a : Int) (t B : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hkernel : Kernel Ω (Avoiders F c) = Anchor a t) :
    F.card + 1 ≤ B := by
  have hground : ∀ S ∈ Avoiders F c, S ⊆ Ω := by
    intro S hS
    exact hF.1 S (Finset.mem_filter.mp hS).1
  have havoid : ∀ S ∈ Avoiders F c, c ∉ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hpair : ∀ S ∈ Avoiders F c, ∀ T ∈ Avoiders F c,
      S ≠ T → IsAP (S ∩ T) := by
    intro S hS T hT hne
    exact hF.2 S (Finset.mem_filter.mp hS).1 T
      (Finset.mem_filter.mp hT).1 hne
  have hcap := step_two_actual_kernel_bound Ω (Avoiders F c) c a t ht hc hm
    hground havoid hcrooked hkernel hpair
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms private_exterior_finset
#print axioms joint_private_card_bound
#print axioms coarse_globally_private
#print axioms joint_tail_bound
#print axioms fine_anchor_global_linear_bound
#print axioms step_two_actual_kernel_bound
#print axioms step_two_avoiders_payment

end JSP233.TwoTraceGlobal
