module

public import Erdos272.Foundation.PrimePowerCapacity

@[expose] public section

namespace JSP233.FiveSixths

open StarCompletion

theorem small_step_kernel_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c d r : Int)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hstep : APGeometry.APAt d r (CommonKernel Ω F c))
    (hd5 : d ≤ 5) (hk : 2 ≤ (CommonKernel Ω F c).card) :
    (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card := by
  have usePower (p e : Nat) (hp : p.Prime) (hd : d = ((p^e : Nat) : Int)) :
      (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card := by
    exact PrimePowerCapacity.represented_kernel_capacity Ω (Avoiders F c) c r p e hp
      hc hm hk
      (fun S hS => hF.1 S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2) hcrooked
      (fun S hS T hT hne => hF.2 S (Finset.mem_filter.mp hS).1
        T (Finset.mem_filter.mp hT).1 hne)
      (by simpa only [←hd,PrivateFinset.Kernel,CommonKernel] using hstep)
  have hdpos : 0 < d := hstep.1
  have hcases : d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 := by omega
  rcases hcases with hd | hd | hd | hd | hd
  · exact usePower 2 0 (by decide) (by simpa using hd)
  · exact usePower 2 1 (by decide) (by simpa using hd)
  · exact usePower 3 1 (by decide) (by simpa using hd)
  · exact usePower 2 2 (by decide) (by simpa using hd)
  · exact usePower 5 1 (by decide) (by simpa using hd)

/-- The entire new five-sixths geometry is proved from actual finite
families. There is no starred extremal premise in this capacity theorem. -/
theorem five_sixths_capacity
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ 5*N/6) :
    (Avoiders F c).card + (CommonKernel Ω F c).card ≤ N := by
  by_contra hneg
  have hNpos : 0 < N := by
    have := Finset.card_pos.mpr (show Ω.Nonempty from ⟨c,hc⟩)
    omega
  have hk : 2 ≤ (CommonKernel Ω F c).card := by omega
  have hKne := Finset.card_pos.mp (show 0 < (CommonKernel Ω F c).card by omega)
  have hKAP := APGeometry.commonKernel_isAP Ω F c hF hm hKne
  obtain ⟨d,r,hstep,_⟩ := (APGeometry.isAP_iff_exists_APAt _).mp hKAP
  have hspan := APGeometry.apAt_card_span hstep hKne
    ((kernel_subset_ambient Ω F c).trans hΩrange)
  have hspan6 : (N : Int) ≤ 6 * (((CommonKernel Ω F c).card : Int)-1) := by omega
  have hd5 : d ≤ 5 := by
    by_contra hno
    have hd6 : 6 ≤ d := by omega
    have hk' : (2 : Int) ≤ ((CommonKernel Ω F c).card : Int) := by exact_mod_cast hk
    nlinarith
  have hcap := small_step_kernel_capacity Ω F c d r hc hF hm hcrooked hstep hd5 hk
  omega

theorem five_sixths_bound
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hcount : (Avoiders F c).card ≤ 5*N/6) : F.card ≤ B := by
  by_cases hm : 2 ≤ (Avoiders F c).card
  · apply completion_payment_of_kernel_capacity Ω F c B hc hF hstar
    rw [hΩcard]
    exact five_sixths_capacity Ω F c N hc hF hm hcrooked hΩcard hΩrange hcount
  · exact at_most_one_avoider_payment Ω F c B hc hF hstar (by omega)

theorem counterexample_region
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int) (N B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hΩcard : Ω.card = N) (hΩrange : Ω ⊆ Finset.Icc 1 (N : Int))
    (hover : B < F.card) :
    N+1 ≤ (Avoiders F c).card + (CommonKernel Ω F c).card ∧
    N - (N-1)/6 ≤ (Avoiders F c).card ∧
    (CommonKernel Ω F c).card ≤ (N-1)/6 + 1 := by
  have hdef := counterexample_forces_kernel_deficit Ω F c B hc hF hstar hover
  have hm : 2 ≤ (Avoiders F c).card := by
    by_contra hneg
    have hpay := at_most_one_avoider_payment Ω F c B hc hF hstar (by omega)
    omega
  have hNpos : 0 < N := by
    have := Finset.card_pos.mpr (show Ω.Nonempty from ⟨c,hc⟩)
    omega
  have hkbound : (CommonKernel Ω F c).card ≤ (N-1)/6 + 1 := by
    by_cases hk : (CommonKernel Ω F c).card ≤ 1
    · omega
    · have hk2 : 2 ≤ (CommonKernel Ω F c).card := by omega
      have hKne := Finset.card_pos.mp (show 0 < (CommonKernel Ω F c).card by omega)
      have hKAP := APGeometry.commonKernel_isAP Ω F c hF hm hKne
      obtain ⟨d,r,hstep,_⟩ := (APGeometry.isAP_iff_exists_APAt _).mp hKAP
      have hspan := APGeometry.apAt_card_span hstep hKne
        ((kernel_subset_ambient Ω F c).trans hΩrange)
      have hd6 : 6 ≤ d := by
        by_contra hneg
        have hcap := small_step_kernel_capacity Ω F c d r hc hF hm hcrooked hstep (by omega) hk2
        omega
      have hk' : (2 : Int) ≤ ((CommonKernel Ω F c).card : Int) := by exact_mod_cast hk2
      have hmul : 6 * (((CommonKernel Ω F c).card : Int)-1) ≤ (N : Int)-1 := by nlinarith
      omega
  exact ⟨by omega,by omega,hkbound⟩

#print axioms small_step_kernel_capacity
#print axioms five_sixths_capacity
#print axioms five_sixths_bound
#print axioms counterexample_region

end JSP233.FiveSixths
