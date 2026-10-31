import Erdos272.Foundation.APGeometry
import Erdos272.Foundation.PrimeKernel
import Erdos272.Foundation.TwoTraceGlobal
import Erdos272.Foundation.ThreeTrace

namespace JSP233.ThreeQuarter

open StarCompletion

/-- Every actual common kernel of step 1, 2 or 3 is payable, without a
large-kernel threshold. The whole omitted family, not just one subgroup,
is counted. -/
theorem small_step_kernel_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c d p : Int)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hstep : APGeometry.APAt d p (CommonKernel Ω F c))
    (hd3 : d ≤ 3) (hk : 2 ≤ (CommonKernel Ω F c).card) :
    (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card := by
  classical
  let D := Avoiders F c
  let K := CommonKernel Ω F c
  have hkK : 2 ≤ K.card := hk
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  let a := K.min' hKne
  have ha : a ∈ K := Finset.min'_mem K hKne
  have hrange : K = (Finset.range K.card).image (fun i : Nat => a+d*(i : Int)) :=
    APGeometry.apAt_eq_range hstep hKne
  have hn : a+d ∈ K := by
    rw [hrange]
    exact Finset.mem_image.mpr ⟨1,Finset.mem_range.mpr (by omega),by simp⟩
  have hcommon : ∀ x ∈ K, ∀ S ∈ D, x ∈ S := by
    intro x hx S hS; exact (Finset.mem_filter.mp hx).2 S hS
  have hground : ∀ S ∈ D, S ⊆ Ω := by
    intro S hS; exact hF.1 S (Finset.mem_filter.mp hS).1
  have havoid : ∀ S ∈ D, c ∉ S := by
    intro S hS; exact (Finset.mem_filter.mp hS).2
  have hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T) := by
    intro S hS T hT hne
    exact hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne
  have hdpos : 0 < d := hstep.1
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  change D.card + K.card + 1 ≤ Ω.card
  rcases hcases with hd | hd | hd
  · subst d
    apply PrivateFinset.same_step_avoiders_card_bound Ω D c 1 a hc hm hground havoid
      hcrooked (hcommon a ha)
    intro S hS T hT hne
    exact PrimeKernel.shared_adjacent_forces_step S T a (hpair S hS T hT hne)
      (Finset.mem_inter.mpr ⟨hcommon a ha S hS,hcommon a ha T hT⟩)
      (Finset.mem_inter.mpr ⟨hcommon (a+1) hn S hS,hcommon (a+1) hn T hT⟩)
  · subst d
    let t := K.card-1
    have ht : 1 ≤ t := by omega
    have htcard : t+1 = K.card := by omega
    have hkernel : PrivateFinset.Kernel Ω D = TwoTrace.Anchor a t := by
      change K = TwoTrace.Anchor a t
      unfold TwoTrace.Anchor
      rw [htcard]
      exact hrange
    exact TwoTraceGlobal.step_two_actual_kernel_bound Ω D c a t ht hc hm
      hground havoid hcrooked hkernel hpair
  · subst d
    let t := K.card-1
    have ht : 1 ≤ t := by omega
    have htcard : t+1 = K.card := by omega
    have hkernel : PrivateFinset.Kernel Ω D = ThreeTrace.Anchor a t := by
      change K = ThreeTrace.Anchor a t
      unfold ThreeTrace.Anchor
      rw [htcard]
      exact hrange
    exact ThreeTrace.step_three_actual_kernel_bound Ω D c a t ht hc hm
      hground havoid hcrooked hkernel hpair

/-- New all-N threshold, derived from true kernel geometry and the joint
global/group-private injection. This theorem does not assume StarBound. -/
theorem three_quarter_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ 3*N/4) :
    (Avoiders F c).card + (CommonKernel Ω F c).card ≤ N := by
  by_contra hneg
  have hNpos : 0 < N := by
    have := Finset.card_pos.mpr (show Ω.Nonempty from ⟨c,hc⟩)
    omega
  have hk : 2 ≤ (CommonKernel Ω F c).card := by omega
  have hKne := Finset.card_pos.mp (show 0 < (CommonKernel Ω F c).card by omega)
  have hKAP := APGeometry.commonKernel_isAP Ω F c hF hm hKne
  obtain ⟨d,p,hstep,hp⟩ := (APGeometry.isAP_iff_exists_APAt _).mp hKAP
  have hKground := (kernel_subset_ambient Ω F c).trans hΩrange
  have hspan := APGeometry.apAt_card_span hstep hKne hKground
  have hdpos : 0 < d := hstep.1
  have hspan4 : (N : Int) ≤ 4 * (((CommonKernel Ω F c).card : Int)-1) := by omega
  have hd3 : d ≤ 3 := by
    by_contra hno
    have hd4 : 4 ≤ d := by omega
    have hk' : (2 : Int) ≤ ((CommonKernel Ω F c).card : Int) := by exact_mod_cast hk
    nlinarith
  have hcap := small_step_kernel_capacity Ω F c d p hc hF hm hcrooked hstep hd3 hk
  omega

theorem three_quarter_bound
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ 3*N/4) : F.card ≤ B := by
  by_cases hm : 2 ≤ (Avoiders F c).card
  · apply completion_payment_of_kernel_capacity Ω F c B hc hF hstar
    rw [hΩcard]
    exact three_quarter_capacity Ω F c N hc hF hm hcrooked hΩcard hΩrange hcount
  · exact at_most_one_avoider_payment Ω F c B hc hF hstar (by omega)

/-- Stronger remaining numerical region, including empty and singleton
kernels. It holds for all N once the explicit starred bound is supplied. -/
theorem counterexample_region
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hover : B < F.card) :
    N+1 ≤ (Avoiders F c).card + (CommonKernel Ω F c).card ∧
    N - (N-1)/4 ≤ (Avoiders F c).card ∧
    (CommonKernel Ω F c).card ≤ (N-1)/4 + 1 := by
  have hdef := counterexample_forces_kernel_deficit Ω F c B hc hF hstar hover
  have hm : 2 ≤ (Avoiders F c).card := by
    by_contra hneg
    have hpay := at_most_one_avoider_payment Ω F c B hc hF hstar (by omega)
    omega
  have hNpos : 0 < N := by
    have := Finset.card_pos.mpr (show Ω.Nonempty from ⟨c,hc⟩)
    omega
  have hkbound : (CommonKernel Ω F c).card ≤ (N-1)/4 + 1 := by
    by_cases hk : (CommonKernel Ω F c).card ≤ 1
    · omega
    · have hk2 : 2 ≤ (CommonKernel Ω F c).card := by omega
      have hKne := Finset.card_pos.mp (show 0 < (CommonKernel Ω F c).card by omega)
      have hKAP := APGeometry.commonKernel_isAP Ω F c hF hm hKne
      obtain ⟨d,p,hstep,hp⟩ := (APGeometry.isAP_iff_exists_APAt _).mp hKAP
      have hspan := APGeometry.apAt_card_span hstep hKne
        ((kernel_subset_ambient Ω F c).trans hΩrange)
      have hd4 : 4 ≤ d := by
        by_contra hneg
        have hcap := small_step_kernel_capacity Ω F c d p hc hF hm hcrooked hstep (by omega) hk2
        omega
      have hk' : (2 : Int) ≤ ((CommonKernel Ω F c).card : Int) := by exact_mod_cast hk2
      have hmul : 4 * (((CommonKernel Ω F c).card : Int)-1) ≤ (N : Int)-1 := by nlinarith
      omega
  exact ⟨by omega,by omega,hkbound⟩

#print axioms small_step_kernel_capacity
#print axioms three_quarter_capacity
#print axioms three_quarter_bound
#print axioms counterexample_region

end JSP233.ThreeQuarter
