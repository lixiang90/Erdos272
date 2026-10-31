import Erdos272.Foundation.TwoTraceGlobal
import Erdos272.Foundation.PrimeKernel

/-! Real step-three common kernels: no near-full-hull or omitter-count
threshold is needed. Coarse members have points private in the entire
family, and the joint selection charges both trace groups to one tail. -/

namespace JSP233.ThreeTrace

open StarCompletion PrivateFinset

noncomputable def Hull (a : Int) (t : Nat) : Finset Int :=
  Finset.Icc a (a + 3 * (t : Int))

def Anchor (a : Int) (t : Nat) : Finset Int :=
  (Finset.range (t+1)).image (fun i : Nat => a + 3 * (i : Int))

theorem mem_hull (a x : Int) (t : Nat) :
    x ∈ Hull a t ↔ a ≤ x ∧ x ≤ a + 3 * (t : Int) := by
  simp [Hull]

theorem mem_anchor (a x : Int) (t : Nat) :
    x ∈ Anchor a t ↔ a ≤ x ∧ x ≤ a + 3 * (t : Int) ∧ 3 ∣ x-a := by
  classical
  simp only [Anchor, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    exact ⟨(i : Int), by omega⟩
  · rintro ⟨hlo, hhi, ⟨q, hq⟩⟩
    have hqlo : 0 ≤ q := by omega
    have hqcast : (q.toNat : Int) = q := Int.toNat_of_nonneg hqlo
    exact ⟨q.toNat, by omega, by omega⟩

theorem anchor_subset_hull (a : Int) (t : Nat) : Anchor a t ⊆ Hull a t := by
  intro x hx
  have h := (mem_anchor a x t).mp hx
  exact (mem_hull a x t).mpr ⟨h.1,h.2.1⟩

theorem anchor_card (a : Int) (t : Nat) : (Anchor a t).card = t+1 := by
  classical
  have hinj : Function.Injective (fun i : Nat => a+3*(i : Int)) := by
    intro i j hij
    change a+3*(i : Int) = a+3*(j : Int) at hij
    have hcast : (i : Int) = (j : Int) := by linarith
    exact Int.ofNat_injective hcast
  rw [Anchor, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem hull_card (a : Int) (t : Nat) : (Hull a t).card = 3*t+1 := by
  rw [Hull, Int.card_Icc]
  omega

theorem hull_anchor_card (a : Int) (t : Nat) :
    (Hull a t).card + 2 = 3 * (Anchor a t).card := by
  rw [hull_card, anchor_card]
  omega

theorem left_mem_anchor (a : Int) (t : Nat) : a ∈ Anchor a t := by
  apply (mem_anchor a a t).mpr
  exact ⟨by omega, by omega, by simp⟩

theorem right_mem_anchor (a : Int) (t : Nat) :
    a + 3*(t : Int) ∈ Anchor a t := by
  apply (mem_anchor a (a+3*(t : Int)) t).mpr
  exact ⟨by omega, by omega, ⟨(t : Int), by omega⟩⟩

theorem second_mem_anchor (a : Int) (t : Nat) (ht : 1 ≤ t) :
    a+3 ∈ Anchor a t := by
  exact (mem_anchor a (a+3) t).mpr
    ⟨by omega, by omega, ⟨1, by omega⟩⟩

theorem hull_APAt (a : Int) (t : Nat) :
    PrivateUnion.APAt 1 a (fun x => x ∈ Hull a t) := by
  refine ⟨by omega, a, a+3*(t : Int), ?_⟩
  intro x
  simp [mem_hull]

theorem anchor_APAt (a : Int) (t : Nat) :
    PrivateUnion.APAt 3 a (fun x => x ∈ Anchor a t) := by
  exact ⟨by omega, a, a+3*(t : Int), fun x => mem_anchor a x t⟩

/-- Any genuine AP containing a three-unit pair has step one or three. -/
theorem step_one_or_three (a : Int) (S : Finset Int)
    (hS : IsAP S) (ha : a ∈ S) (ha2 : a+3 ∈ S) :
    PrivateUnion.APAt 1 a (fun x => x ∈ S) ∨
    PrivateUnion.APAt 3 a (fun x => x ∈ S) := by
  rcases (isAP_iff_predicate S).mp hS with ⟨q, p, hq, _⟩
  have hq' := PrivateUnion.APAt_rebase q p a _ hq ha
  rcases hq' with ⟨hqpos, lo, hi, hrep⟩
  have hdiv : q ∣ 3 := by
    simpa using ((hrep (a+3)).mp ha2).2.2
  have hle : q ≤ 3 := Int.le_of_dvd (by omega) hdiv
  have heq : q = 1 ∨ q = 3 := PrimeKernel.positive_divisor_three q hqpos hdiv
  rcases heq with rfl | rfl
  · exact Or.inl ⟨hqpos,lo,hi,hrep⟩
  · exact Or.inr ⟨hqpos,lo,hi,hrep⟩

theorem hull_subset_of_step_one (a : Int) (t : Nat) (S : Finset Int)
    (hS : PrivateUnion.APAt 1 a (fun x => x ∈ S))
    (ha : a ∈ S) (hb : a+3*(t : Int) ∈ S) : Hull a t ⊆ S := by
  rcases hS with ⟨_,lo,hi,hrep⟩
  have ha' := (hrep a).mp ha
  have hb' := (hrep _).mp hb
  intro x hx
  have hx' := (mem_hull a x t).mp hx
  exact (hrep x).mpr ⟨by omega,by omega,by simp⟩

theorem trace_eq_anchor_of_step_three (a : Int) (t : Nat) (S : Finset Int)
    (hS : PrivateUnion.APAt 3 a (fun x => x ∈ S))
    (ha : a ∈ S) (hb : a+3*(t : Int) ∈ S) :
    S ∩ Hull a t = Anchor a t := by
  rcases hS with ⟨_,lo,hi,hrep⟩
  have ha' := (hrep a).mp ha
  have hb' := (hrep _).mp hb
  ext x
  constructor
  · intro hx
    have hxS := (hrep x).mp (Finset.mem_inter.mp hx).1
    have hxI := (mem_hull a x t).mp (Finset.mem_inter.mp hx).2
    exact (mem_anchor a x t).mpr ⟨hxI.1,hxI.2,hxS.2.2⟩
  · intro hx
    have hx' := (mem_anchor a x t).mp hx
    exact Finset.mem_inter.mpr
      ⟨(hrep x).mpr ⟨by omega,by omega,hx'.2.2⟩,
       (mem_hull a x t).mpr ⟨hx'.1,hx'.2.1⟩⟩

/-- With one fine member, every actual member has exactly one of the two
traces on the hull. The common anchor alone does not imply this dichotomy. -/
theorem two_trace_classification (a : Int) (t : Nat) (ht : 1 ≤ t)
    (S T : Finset Int) (hKS : Anchor a t ⊆ S) (hKT : Anchor a t ⊆ T)
    (hf : Hull a t ⊆ S) (hpair : IsAP (S ∩ T)) :
    Hull a t ⊆ T ∨ T ∩ Hull a t = Anchor a t := by
  have ha := left_mem_anchor a t
  have ha2 := second_mem_anchor a t ht
  have hb := right_mem_anchor a t
  have hcommon : a ∈ S ∩ T := Finset.mem_inter.mpr ⟨hKS ha,hKT ha⟩
  have hcommon2 : a+3 ∈ S ∩ T := Finset.mem_inter.mpr ⟨hKS ha2,hKT ha2⟩
  have hcommonb : a+3*(t : Int) ∈ S ∩ T :=
    Finset.mem_inter.mpr ⟨hKS hb,hKT hb⟩
  rcases step_one_or_three a (S ∩ T) hpair hcommon hcommon2 with h1 | h2
  · exact Or.inl (fun x hx => (Finset.mem_inter.mp
      (hull_subset_of_step_one a t _ h1 hcommon hcommonb hx)).2)
  · have he := trace_eq_anchor_of_step_three a t (S ∩ T) h2 hcommon hcommonb
    apply Or.inr
    ext x
    have hSI : (x ∈ (S ∩ T) ∩ Hull a t) ↔ x ∈ T ∩ Hull a t := by
      simp only [Finset.mem_inter]
      constructor
      · exact fun h => ⟨h.1.2,h.2⟩
      · exact fun h => ⟨⟨hf h.2,h.1⟩,h.2⟩
    rw [← he]
    exact hSI.symm

/-- A finite group with genuine AP core traces and genuine same-step pair
intersections is charged injectively to its actual exterior ground points.
This also includes groups with zero or one member. -/
theorem group_le_tail (Ω I : Finset Int) (D : Finset (Finset Int)) (d a : Int)
    (haI : a ∈ I) (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S) (haD : ∀ S ∈ D, a ∈ S)
    (hcore : ∀ S ∈ D, PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ I))
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ T)) :
    D.card ≤ (Ω \ I).card := by
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
  have hr := PrivateUnion.family_le_exterior_capacity d a A
    (fun x => x ∈ I) (Ω \ I).toList hcrookedA haI hpA hcoreA hpairA
    (by
      intro i x hx hnx
      exact Finset.mem_toList.mpr (Finset.mem_sdiff.mpr
        ⟨hground _ (e i).property hx,hnx⟩))
  simpa only [Finset.length_toList] using hr

theorem one_mem_hull (a : Int) (t : Nat) (ht : 1 ≤ t) :
    a+1 ∈ Hull a t := by
  exact (mem_hull a (a+1) t).mpr ⟨by omega,by omega⟩

theorem one_not_mem_anchor (a : Int) (t : Nat) : a+1 ∉ Anchor a t := by
  intro hx
  have hd := ((mem_anchor a (a+1) t).mp hx).2.2
  norm_num at hd

/-- Fine pair intersections contain an actual unit pair, which forces step
one. This is an implication from ordinary AP legality. -/
theorem fine_pair_step_one (a : Int) (t : Nat) (ht : 1 ≤ t)
    (S T : Finset Int) (hS : Hull a t ⊆ S) (hT : Hull a t ⊆ T)
    (hpair : IsAP (S ∩ T)) :
    PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
  have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
  have hp := PrivateUnion.IsAP_same_step_of_adjacent 1 a
    (fun x => x ∈ S) (fun x => x ∈ S ∧ x ∈ T) (by omega)
    (by simpa only [Finset.mem_inter] using (isAP_iff_predicate _).mp hpair)
    ⟨hS haI,hT haI⟩ ⟨hS (one_mem_hull a t ht),hT (one_mem_hull a t ht)⟩
    (by intro x hx; exact hx.1)
    (by intro x hlo hhi hx; omega)
  exact hp

/-- A nonfine member prevents a step-one intersection. Thus every ordinary
AP intersection of two anchor-containing members is really of step three. -/
theorem nonfine_pair_step_three (a : Int) (t : Nat) (ht : 1 ≤ t)
    (S T : Finset Int) (hKS : Anchor a t ⊆ S) (hKT : Anchor a t ⊆ T)
    (hS : ¬ Hull a t ⊆ S) (hpair : IsAP (S ∩ T)) :
    PrivateUnion.APAt 3 a (fun x => x ∈ S ∧ x ∈ T) := by
  have ha : a ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (left_mem_anchor a t),hKT (left_mem_anchor a t)⟩
  have hb : a+3*(t : Int) ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (right_mem_anchor a t),hKT (right_mem_anchor a t)⟩
  have ha2 : a+3 ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (second_mem_anchor a t ht),hKT (second_mem_anchor a t ht)⟩
  rcases step_one_or_three a _ hpair ha ha2 with h1 | h2
  · exact False.elim (hS (fun x hx => (Finset.mem_inter.mp
      (hull_subset_of_step_one a t _ h1 ha hb hx)).1))
  · simpa only [Finset.mem_inter] using h2

theorem no_fine_same_step (a : Int) (t : Nat) (ht : 1 ≤ t)
    (D : Finset (Finset Int)) (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hnf : ∀ S ∈ D, ¬ Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt 3 a (fun x => x ∈ S ∧ x ∈ T) := by
  intro S hS T hT hne
  exact nonfine_pair_step_three a t ht S T (hK S hS) (hK T hT)
    (hnf S hS) (hpair S hS T hT hne)

/-- One fine member forces a genuine two-trace decomposition throughout D. -/
theorem family_two_traces (a : Int) (t : Nat) (ht : 1 ≤ t)
    (D : Finset (Finset Int)) (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    ∀ T ∈ D, Hull a t ⊆ T ∨ T ∩ Hull a t = Anchor a t := by
  rcases hf with ⟨S,hS,hf⟩
  intro T hT
  by_cases he : S = T
  · subst T
    exact Or.inl hf
  · exact two_trace_classification a t ht S T (hK S hS) (hK T hT)
      hf (hpair S hS T hT he)


/-- A coarse member has a private exterior point with respect to all of D,
since all its intersections, even with fine members, have step three. -/
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
    have hstep := nonfine_pair_step_three a t ht S T (hK S hS) (hK T hT)
      hSnf (hpair T hT hne)
    have he := trace_eq_anchor_of_step_three a t (S ∩ T)
      (by simpa only [Finset.mem_inter] using hstep)
      (Finset.mem_inter.mpr ⟨haD S hS,haD T hT⟩)
      (Finset.mem_inter.mpr
        ⟨hK S hS (right_mem_anchor a t),hK T hT (right_mem_anchor a t)⟩)
    ext x
    rw [← he]
    simp only [Finset.mem_inter]
    exact ⟨fun hx => ⟨⟨hx.1,hTf hx.2⟩,hx.2⟩,
      fun hx => ⟨hx.1.1,hx.2⟩⟩
  have hcore : PrivateUnion.APAt 3 a (fun x => x ∈ S ∧ x ∈ Hull a t) := by
    apply PrivateUnion.APAt_congr 3 a _ _ (anchor_APAt a t)
    intro x
    rw [← htrace]
    exact Finset.mem_inter
  exact TwoTraceGlobal.private_exterior_finset D S (Hull a t) 3 a (haD S hS) haI haD
    hcrooked hcore (fun T hT hne =>
      nonfine_pair_step_three a t ht S T (hK S hS) (hK T hT) hSnf
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
  apply TwoTraceGlobal.joint_private_card_bound Ω (Hull a t) D (fun S => Hull a t ⊆ S) hground
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
    rcases TwoTraceGlobal.private_exterior_finset Fine S (Hull a t) 1 a (hSI haI) haI haF
      (hcrooked S hS) hcore hp with ⟨x,hx,hxI,hpriv⟩
    refine ⟨x,hx,hxI,?_⟩
    intro T hT hne hclass
    have hTI := hclass.resolve_left (not_not.mpr hSI)
    exact hpriv T (Finset.mem_filter.mpr ⟨hT,hTI⟩) hne
  · rcases coarse_globally_private D S a t ht hS (hcrooked S hS) hK hf
      (hpair S hS) hSI with ⟨x,hx,hxI,hpriv⟩
    exact ⟨x,hx,hxI,fun T hT hne _ => hpriv T hT hne⟩

/-- A real root removes one slot, and the hull has size `3 k - 2`.
The joint assignment therefore proves `h + 3 k <= N+1` in the fine branch. -/
theorem fine_anchor_global_linear_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + 3 * (Anchor a t).card ≤ Ω.card + 1 := by
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

/-- Every actual step-three common kernel with at least two points gives
strict payment, with no large-kernel or omitted-family-size threshold. -/
theorem step_three_actual_kernel_bound
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
    exact same_step_avoiders_card_bound Ω D c 3 a hc hm hground havoid
      hcrooked hp (no_fine_same_step a t ht D hK hnf hpair)

/-- The geometric class is connected to the original legal family. Yang's
starred bound remains the only unproved extremal premise, explicitly named. -/
theorem step_three_avoiders_payment
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
  have hcap := step_three_actual_kernel_bound Ω (Avoiders F c) c a t ht hc hm
    hground havoid hcrooked hkernel hpair
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms TwoTraceGlobal.private_exterior_finset
#print axioms TwoTraceGlobal.joint_private_card_bound
#print axioms coarse_globally_private
#print axioms joint_tail_bound
#print axioms fine_anchor_global_linear_bound
#print axioms step_three_actual_kernel_bound
#print axioms step_three_avoiders_payment


end JSP233.ThreeTrace
