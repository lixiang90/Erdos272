module

public import Erdos272.Foundation.APGeometry
public import Erdos272.Foundation.TwoTrace
public import Erdos272.Foundation.PrimeKernel
public import Erdos272.Foundation.SmallGround

@[expose] public section

/-! The complete geometric/counting part of the round-20 all-N linear
omitter theorem. The final original-family bound has precisely the named
starred bound as its unproved extremal parameter. -/

namespace JSP233.LinearThreshold

open StarCompletion

theorem large_kernel_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hN : 6 ≤ N) (hlarge : N/3 < (CommonKernel Ω F c).card) :
    (Avoiders F c).card + (CommonKernel Ω F c).card ≤ N := by
  classical
  let D := Avoiders F c
  let K := CommonKernel Ω F c
  have hk : 3 ≤ K.card := by dsimp [K]; omega
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  have hKAP : IsAP K := APGeometry.commonKernel_isAP Ω F c hF hm hKne
  have hKground : K ⊆ Finset.Icc 1 (N : Int) :=
    (kernel_subset_ambient Ω F c).trans hΩrange
  obtain ⟨d,a,b,hstep,hdpos,hd3,ha,hn,hb,hbounds,hspan,hrange⟩ :=
    APGeometry.isAP_large_card_geometry hKAP hN hlarge hKground
  have hground : ∀ S ∈ D, S ⊆ Ω := by
    intro S hS; exact hF.1 S (Finset.mem_filter.mp hS).1
  have havoid : ∀ S ∈ D, c ∉ S := by
    intro S hS; exact (Finset.mem_filter.mp hS).2
  have hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T) := by
    intro S hS T hT hne
    exact hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne
  have hcommon : ∀ x ∈ K, ∀ S ∈ D, x ∈ S := by
    intro x hx S hS; exact (Finset.mem_filter.mp hx).2 S hS
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  change D.card + K.card ≤ N
  rcases hcases with hd | hd | hd
  · subst d
    have hp : ∀ S ∈ D, a ∈ S := hcommon a ha
    have hstepPair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
        PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
      intro S hS T hT hne
      exact PrimeKernel.shared_adjacent_forces_step S T a (hpair S hS T hT hne)
        (Finset.mem_inter.mpr ⟨hp S hS,hp T hT⟩)
        (Finset.mem_inter.mpr ⟨hcommon (a+1) hn S hS,hcommon (a+1) hn T hT⟩)
    have hcap := PrivateFinset.same_step_avoiders_card_bound Ω D c 1 a hc hm
      hground havoid hcrooked hp hstepPair
    change D.card + K.card + 1 ≤ Ω.card at hcap
    omega
  · subst d
    let t := K.card - 1
    have ht : 1 ≤ t := by omega
    have htcard : t+1 = K.card := by omega
    have hkernel : PrivateFinset.Kernel Ω D = TwoTrace.Anchor a t := by
      change K = TwoTrace.Anchor a t
      unfold TwoTrace.Anchor
      rw [htcard]
      exact hrange
    have hlarge' : Ω.card ≤ 3 * (PrivateFinset.Kernel Ω D).card := by
      change Ω.card ≤ 3 * K.card
      change N/3 < K.card at hlarge
      omega
    have hcap := TwoTrace.large_actual_kernel_bound Ω D c a t ht hc hm
      hground havoid hcrooked hkernel hpair hlarge'
    change D.card + K.card ≤ Ω.card at hcap
    omega
  · subst d
    have hab : a ≤ b := (hbounds b hb).1
    have hIcard : ((Finset.Icc a b).card : Int) = b-a+1 := by
      have hcI := Int.card_Icc_of_le (a := a) (b := b) (by omega)
      omega
    have hnear : Ω.card ≤ (Finset.Icc a b).card + 1 := by
      change N/3 < K.card at hlarge
      omega
    have hp : ∀ S ∈ D, a ∈ S := hcommon a ha
    have hstepPair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T →
        PrivateUnion.APAt 3 a (fun x => x ∈ S ∧ x ∈ T) := by
      intro S hS T hT hne
      apply PrimeKernel.shared_three_near_full_forces_step Ω S T c a b hc
        (hground S hS) (havoid S hS) (hcrooked S hS) hab hnear (hpair S hS T hT hne)
      · exact Finset.mem_inter.mpr ⟨hp S hS,hp T hT⟩
      · exact Finset.mem_inter.mpr ⟨hcommon (a+3) hn S hS,hcommon (a+3) hn T hT⟩
      · exact Finset.mem_inter.mpr ⟨hcommon b hb S hS,hcommon b hb T hT⟩
    have hcap := PrivateFinset.same_step_avoiders_card_bound Ω D c 3 a hc hm
      hground havoid hcrooked hp hstepPair
    change D.card + K.card + 1 ≤ Ω.card at hcap
    omega

/-- The actual capacity inequality for all N; no starred upper bound is
needed in this geometric/counting theorem. -/
theorem linear_omitter_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ (2*N+2)/3) :
    (Avoiders F c).card + (CommonKernel Ω F c).card ≤ N := by
  classical
  by_cases hN : 6 ≤ N
  · by_cases hk : N/3 < (CommonKernel Ω F c).card
    · exact large_kernel_capacity Ω F c N hc hF hm hcrooked hΩcard hΩrange hN hk
    · omega
  · have hsmall : Ω.card ≤ 5 := by omega
    by_cases htiny : Ω.card ≤ 3
    · exact False.elim (SmallGround.no_two_crooked_omitters_on_tiny_ground
        Ω F c hc hF htiny hm hcrooked)
    · by_cases hk : (CommonKernel Ω F c).card ≤ 1
      · omega
      · have hK2 : 2 ≤ (CommonKernel Ω F c).card := by omega
        have hKne := Finset.card_pos.mp (show 0 < (CommonKernel Ω F c).card by omega)
        have hKAP := APGeometry.commonKernel_isAP Ω F c hF hm hKne
        have hcap := SmallGround.small_ground_ap_core_capacity Ω (CommonKernel Ω F c)
          (Avoiders F c) c hc hsmall hm hKAP hK2
          (by intro S hS; exact hF.1 S (Finset.mem_filter.mp hS).1)
          (by intro S hS; exact (Finset.mem_filter.mp hS).2) hcrooked
          (by intro S hS x hx; exact (Finset.mem_filter.mp hx).2 S hS)
        omega

/-- Best round-20 linear threshold, with the already-known starred bound
kept as a single explicit external premise. Every other step is proved. -/
theorem linear_omitter_bound
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ (2*N+2)/3) : F.card ≤ B := by
  by_cases hm : 2 ≤ (Avoiders F c).card
  · apply completion_payment_of_kernel_capacity Ω F c B hc hF hstar
    rw [hΩcard]
    exact linear_omitter_capacity Ω F c N hc hF hm hcrooked hΩcard hΩrange hcount
  · exact at_most_one_avoider_payment Ω F c B hc hF hstar (by omega)

#print axioms large_kernel_capacity
#print axioms linear_omitter_capacity
#print axioms linear_omitter_bound

end JSP233.LinearThreshold
