import Erdos272.Foundation.PrivateFinset
import Mathlib.Data.Int.Interval

/-!
The actual two-trace mechanism for a common progression of step two.
All slots in the counting theorem are actual exterior integer points.
Neither group-private-point injections nor numerical capacities are inputs.
-/

namespace JSP233.TwoTrace

open StarCompletion PrivateFinset

noncomputable def Hull (a : Int) (t : Nat) : Finset Int :=
  Finset.Icc a (a + 2 * (t : Int))

def Anchor (a : Int) (t : Nat) : Finset Int :=
  (Finset.range (t+1)).image (fun i : Nat => a + 2 * (i : Int))

theorem mem_hull (a x : Int) (t : Nat) :
    x ∈ Hull a t ↔ a ≤ x ∧ x ≤ a + 2 * (t : Int) := by
  simp [Hull]

theorem mem_anchor (a x : Int) (t : Nat) :
    x ∈ Anchor a t ↔ a ≤ x ∧ x ≤ a + 2 * (t : Int) ∧ 2 ∣ x-a := by
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
  have hinj : Function.Injective (fun i : Nat => a+2*(i : Int)) := by
    intro i j hij
    change a+2*(i : Int) = a+2*(j : Int) at hij
    have hcast : (i : Int) = (j : Int) := by linarith
    exact Int.ofNat_injective hcast
  rw [Anchor, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem hull_card (a : Int) (t : Nat) : (Hull a t).card = 2*t+1 := by
  rw [Hull, Int.card_Icc]
  omega

theorem hull_anchor_card (a : Int) (t : Nat) :
    (Hull a t).card + 1 = 2 * (Anchor a t).card := by
  rw [hull_card, anchor_card]
  omega

theorem left_mem_anchor (a : Int) (t : Nat) : a ∈ Anchor a t := by
  apply (mem_anchor a a t).mpr
  exact ⟨by omega, by omega, by simp⟩

theorem right_mem_anchor (a : Int) (t : Nat) :
    a + 2*(t : Int) ∈ Anchor a t := by
  apply (mem_anchor a (a+2*(t : Int)) t).mpr
  exact ⟨by omega, by omega, ⟨(t : Int), by omega⟩⟩

theorem second_mem_anchor (a : Int) (t : Nat) (ht : 1 ≤ t) :
    a+2 ∈ Anchor a t := by
  exact (mem_anchor a (a+2) t).mpr
    ⟨by omega, by omega, ⟨1, by omega⟩⟩

theorem hull_APAt (a : Int) (t : Nat) :
    PrivateUnion.APAt 1 a (fun x => x ∈ Hull a t) := by
  refine ⟨by omega, a, a+2*(t : Int), ?_⟩
  intro x
  simp [mem_hull]

theorem anchor_APAt (a : Int) (t : Nat) :
    PrivateUnion.APAt 2 a (fun x => x ∈ Anchor a t) := by
  exact ⟨by omega, a, a+2*(t : Int), fun x => mem_anchor a x t⟩

/-- Any genuine AP containing a two-unit pair has step one or two. -/
theorem step_one_or_two (a : Int) (S : Finset Int)
    (hS : IsAP S) (ha : a ∈ S) (ha2 : a+2 ∈ S) :
    PrivateUnion.APAt 1 a (fun x => x ∈ S) ∨
    PrivateUnion.APAt 2 a (fun x => x ∈ S) := by
  rcases (isAP_iff_predicate S).mp hS with ⟨q, p, hq, _⟩
  have hq' := PrivateUnion.APAt_rebase q p a _ hq ha
  rcases hq' with ⟨hqpos, lo, hi, hrep⟩
  have hdiv : q ∣ 2 := by
    simpa using ((hrep (a+2)).mp ha2).2.2
  have hle : q ≤ 2 := Int.le_of_dvd (by omega) hdiv
  have heq : q = 1 ∨ q = 2 := by omega
  rcases heq with rfl | rfl
  · exact Or.inl ⟨hqpos,lo,hi,hrep⟩
  · exact Or.inr ⟨hqpos,lo,hi,hrep⟩

theorem hull_subset_of_step_one (a : Int) (t : Nat) (S : Finset Int)
    (hS : PrivateUnion.APAt 1 a (fun x => x ∈ S))
    (ha : a ∈ S) (hb : a+2*(t : Int) ∈ S) : Hull a t ⊆ S := by
  rcases hS with ⟨_,lo,hi,hrep⟩
  have ha' := (hrep a).mp ha
  have hb' := (hrep _).mp hb
  intro x hx
  have hx' := (mem_hull a x t).mp hx
  exact (hrep x).mpr ⟨by omega,by omega,by simp⟩

theorem trace_eq_anchor_of_step_two (a : Int) (t : Nat) (S : Finset Int)
    (hS : PrivateUnion.APAt 2 a (fun x => x ∈ S))
    (ha : a ∈ S) (hb : a+2*(t : Int) ∈ S) :
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
  have hcommon2 : a+2 ∈ S ∩ T := Finset.mem_inter.mpr ⟨hKS ha2,hKT ha2⟩
  have hcommonb : a+2*(t : Int) ∈ S ∩ T :=
    Finset.mem_inter.mpr ⟨hKS hb,hKT hb⟩
  rcases step_one_or_two a (S ∩ T) hpair hcommon hcommon2 with h1 | h2
  · exact Or.inl (fun x hx => (Finset.mem_inter.mp
      (hull_subset_of_step_one a t _ h1 hcommon hcommonb hx)).2)
  · have he := trace_eq_anchor_of_step_two a t (S ∩ T) h2 hcommon hcommonb
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
AP intersection of two anchor-containing members is really of step two. -/
theorem nonfine_pair_step_two (a : Int) (t : Nat) (ht : 1 ≤ t)
    (S T : Finset Int) (hKS : Anchor a t ⊆ S) (hKT : Anchor a t ⊆ T)
    (hS : ¬ Hull a t ⊆ S) (hpair : IsAP (S ∩ T)) :
    PrivateUnion.APAt 2 a (fun x => x ∈ S ∧ x ∈ T) := by
  have ha : a ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (left_mem_anchor a t),hKT (left_mem_anchor a t)⟩
  have hb : a+2*(t : Int) ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (right_mem_anchor a t),hKT (right_mem_anchor a t)⟩
  have ha2 : a+2 ∈ S ∩ T := Finset.mem_inter.mpr
    ⟨hKS (second_mem_anchor a t ht),hKT (second_mem_anchor a t ht)⟩
  rcases step_one_or_two a _ hpair ha ha2 with h1 | h2
  · exact False.elim (hS (fun x hx => (Finset.mem_inter.mp
      (hull_subset_of_step_one a t _ h1 ha hb hx)).1))
  · simpa only [Finset.mem_inter] using h2

theorem no_fine_same_step (a : Int) (t : Nat) (ht : 1 ≤ t)
    (D : Finset (Finset Int)) (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hnf : ∀ S ∈ D, ¬ Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt 2 a (fun x => x ∈ S ∧ x ∈ T) := by
  intro S hS T hT hne
  exact nonfine_pair_step_two a t ht S T (hK S hS) (hK T hT)
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

/-- The finite family is split by actual containment of the full hull.
Every group has a private exterior point for each crooked member, derived
by the AP union theorem. The same actual tail may pay once in each group. -/
theorem two_groups_tail_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card ≤ 2 * (Ω \ Hull a t).card := by
  classical
  let Fine := D.filter (fun S => Hull a t ⊆ S)
  let Coarse := D.filter (fun S => ¬ Hull a t ⊆ S)
  have htr := family_two_traces a t ht D hK hf hpair
  have haI : a ∈ Hull a t := anchor_subset_hull a t (left_mem_anchor a t)
  have hFine := group_le_tail Ω (Hull a t) Fine 1 a haI
    (by intro S hS; exact hground S (Finset.mem_filter.mp hS).1)
    (by intro S hS; exact hcrooked S (Finset.mem_filter.mp hS).1)
    (by
      intro S hS
      exact (Finset.mem_filter.mp hS).2 haI)
    (by
      intro S hS
      apply PrivateUnion.APAt_congr 1 a _ _ (hull_APAt a t)
      intro x
      constructor
      · intro hx
        exact ⟨(Finset.mem_filter.mp hS).2 hx,hx⟩
      · exact fun hx => hx.2)
    (by
      intro S hS T hT hne
      have hSf := Finset.mem_filter.mp hS
      have hTf := Finset.mem_filter.mp hT
      exact fine_pair_step_one a t ht S T hSf.2 hTf.2
        (hpair S hSf.1 T hTf.1 hne))
  have hCoarse := group_le_tail Ω (Hull a t) Coarse 2 a haI
    (by intro S hS; exact hground S (Finset.mem_filter.mp hS).1)
    (by intro S hS; exact hcrooked S (Finset.mem_filter.mp hS).1)
    (by
      intro S hS
      exact hK S (Finset.mem_filter.mp hS).1 (left_mem_anchor a t))
    (by
      intro S hS
      have hSf := Finset.mem_filter.mp hS
      have he : S ∩ Hull a t = Anchor a t := (htr S hSf.1).resolve_left hSf.2
      apply PrivateUnion.APAt_congr 2 a _ _ (anchor_APAt a t)
      intro x
      rw [← he]
      exact Finset.mem_inter)
    (by
      intro S hS T hT hne
      have hSf := Finset.mem_filter.mp hS
      have hTf := Finset.mem_filter.mp hT
      exact nonfine_pair_step_two a t ht S T (hK S hSf.1) (hK T hTf.1)
        hSf.2 (hpair S hSf.1 T hTf.1 hne))
  have hpartition : Fine.card + Coarse.card = D.card :=
    Finset.card_filter_add_card_filter_not (s := D) (fun S => Hull a t ⊆ S)
  omega

/-- Avoiding a genuine ground point removes that point from both groups'
tail lists. A fine member also proves that the root is outside the hull. -/
theorem two_groups_avoiders_tail_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (c a : Int) (t : Nat) (ht : 1 ≤ t)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card ≤ 2 * ((Ω.erase c) \ Hull a t).card := by
  apply two_groups_tail_bound (Ω.erase c) D a t ht
  · intro S hS x hx
    exact Finset.mem_erase.mpr
      ⟨by intro he; exact havoid S hS (he ▸ hx),hground S hS hx⟩
  · exact hcrooked
  · exact hK
  · exact hf
  · exact hpair

/-- The geometric estimate before imposing the large-kernel threshold:
`h + 4 k <= 2 N`, or equivalently `h <= 2 (N - 2 k)`. -/
theorem fine_anchor_linear_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (c a : Int) (t : Nat) (ht : 1 ≤ t) (hc : c ∈ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + 4 * (Anchor a t).card ≤ 2 * Ω.card := by
  have htail := two_groups_avoiders_tail_bound Ω D c a t ht hground havoid
    hcrooked hK hf hpair
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

/-- Complete long-step-two payment in the fine branch. The scalar
large-kernel condition is the only counting threshold supplied as input;
the two group capacities and the hull/kernel sizes are proved internally. -/
theorem fine_large_anchor_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (c a : Int) (t : Nat) (ht : 1 ≤ t) (hc : c ∈ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hK : ∀ S ∈ D, Anchor a t ⊆ S)
    (hf : ∃ S ∈ D, Hull a t ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hlarge : Ω.card ≤ 3 * (Anchor a t).card) :
    D.card + (Anchor a t).card ≤ Ω.card := by
  have hlinear := fine_anchor_linear_bound Ω D c a t ht hc hground havoid
    hcrooked hK hf hpair
  omega

/-- The step-two anchor need not be an arbitrary subset here: requiring
it to equal the actual common kernel gives precisely the extremal payment
used by root completion. No fine/nonfine case is left as a hypothesis. -/
theorem large_actual_kernel_bound (Ω : Finset Int) (D : Finset (Finset Int))
    (c a : Int) (t : Nat) (ht : 1 ≤ t) (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hkernel : Kernel Ω D = Anchor a t)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hlarge : Ω.card ≤ 3 * (Kernel Ω D).card) :
    D.card + (Kernel Ω D).card ≤ Ω.card := by
  classical
  have hK : ∀ S ∈ D, Anchor a t ⊆ S := by
    intro S hS x hx
    rw [← hkernel] at hx
    exact (Finset.mem_filter.mp hx).2 S hS
  by_cases hf : ∃ S ∈ D, Hull a t ⊆ S
  · rw [hkernel] at hlarge ⊢
    exact fine_large_anchor_bound Ω D c a t ht hc hground havoid hcrooked
      hK hf hpair hlarge
  · have hnf : ∀ S ∈ D, ¬ Hull a t ⊆ S := by
      intro S hS hfull
      exact hf ⟨S,hS,hfull⟩
    have hp : ∀ S ∈ D, a ∈ S := fun S hS => hK S hS (left_mem_anchor a t)
    exact same_step_card_bound Ω D 2 a hm hground hcrooked hp
      (no_fine_same_step a t ht D hK hnf hpair)

/-- A genuine counterexample with step-two common kernel must have a fine
member. Its actual two-group exterior payment also forces `3 k + 1 <= N`,
including the strict integer improvement when N is a multiple of three.
The starred extremal theorem is an explicit premise in this corollary. -/
theorem counterexample_step_two_constraints
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a : Int) (t B : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hkernel : Kernel Ω (Avoiders F c) = Anchor a t)
    (hover : B < F.card) :
    (∃ S ∈ Avoiders F c, Hull a t ⊆ S) ∧
    (Avoiders F c).card + 4 * (CommonKernel Ω F c).card ≤ 2 * Ω.card ∧
    3 * (CommonKernel Ω F c).card + 1 ≤ Ω.card := by
  classical
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
  have hf : ∃ S ∈ Avoiders F c, Hull a t ⊆ S := by
    by_contra hn
    have hnf : ∀ S ∈ Avoiders F c, ¬ Hull a t ⊆ S := by
      intro S hS hfull
      exact hn ⟨S,hS,hfull⟩
    have hp : ∀ S ∈ Avoiders F c, a ∈ S :=
      fun S hS => hK S hS (left_mem_anchor a t)
    have hpay := same_step_avoiders_payment Ω F c 2 a B hc hF hstar hm
      hcrooked hp (no_fine_same_step a t ht (Avoiders F c) hK hnf hpair)
    omega
  have hlinear := fine_anchor_linear_bound Ω (Avoiders F c) c a t ht hc
    hground havoid hcrooked hK hf hpair
  have hk : CommonKernel Ω F c = Anchor a t := hkernel
  have hlinear' : (Avoiders F c).card +
      4 * (CommonKernel Ω F c).card ≤ 2 * Ω.card := by
    rw [hk]
    exact hlinear
  have hdeficit := counterexample_forces_kernel_deficit Ω F c B hc hF hstar hover
  exact ⟨hf,hlinear',by omega⟩

#print axioms mem_anchor
#print axioms anchor_card
#print axioms hull_anchor_card
#print axioms step_one_or_two
#print axioms two_trace_classification
#print axioms group_le_tail
#print axioms nonfine_pair_step_two
#print axioms family_two_traces
#print axioms two_groups_tail_bound
#print axioms two_groups_avoiders_tail_bound
#print axioms fine_anchor_linear_bound
#print axioms fine_large_anchor_bound
#print axioms large_actual_kernel_bound
#print axioms counterexample_step_two_constraints

end JSP233.TwoTrace
