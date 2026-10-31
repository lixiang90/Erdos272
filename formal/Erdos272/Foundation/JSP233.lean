import Erdos272.Foundation.DyadicFinset
import Erdos272.Foundation.LinearThreshold
import Erdos272.Foundation.PrivatePairExistence
import Erdos272.Foundation.StaircaseCertificate
import Erdos272.Foundation.StaircaseGeometry
import Erdos272.Foundation.StaircaseSupply
import Erdos272.Foundation.Staircase249
import Erdos272.Foundation.StaircaseTail
import Erdos272.Foundation.StaircaseThin
import Erdos272.Foundation.ThreeQuarter
import Erdos272.Foundation.TwoTraceStrict
import Erdos272.Foundation.PrimeCapacity
import Erdos272.Foundation.FiveSixths

/-!
Concrete [N] interfaces. The all-N linear omitter theorem now has its
entire new geometric/counting proof. The starred upper bound remains
a deliberately named external premise, rather than a new axiom.
-/

namespace JSP233

open StarCompletion

def Ground (N : Nat) : Finset Int :=
  (Finset.range N).image (fun i : Nat => (i : Int) + 1)

def B (N : Nat) : Nat := N.choose 2 + 1 + (N - 1) / 4

theorem ground_card (N : Nat) : (Ground N).card = N := by
  rw [Ground, Finset.card_image_of_injective]
  · exact Finset.card_range N
  · intro a b hab
    change (a : Int) + 1 = (b : Int) + 1 at hab
    omega

theorem mem_ground (N : Nat) (x : Int) :
    x ∈ Ground N ↔ 1 ≤ x ∧ x ≤ (N : Int) := by
  simp only [Ground, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hx
    refine ⟨(x - 1).toNat, ?_, ?_⟩ <;> omega

/-- All N, actual finite family, actual eight-member dyadic pattern.
The starred bound is an explicit external theorem parameter. -/
theorem dyadic_pattern_bound (N : Nat) (F : Finset (Finset Int))
    (c : Int) (j : Nat) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hpattern : ∀ s : Fin 8,
      DyadicFinset.stencilSet c (DyadicStencil.step j) s ∈ F) :
    F.card ≤ B N := by
  exact DyadicFinset.actual_dyadic_stencil_payment (Ground N) F c j (B N)
    hlegal hstar hcrooked hpattern

theorem dyadic_pattern_strict_bound (N : Nat) (F : Finset (Finset Int))
    (c : Int) (j : Nat) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hpattern : ∀ s : Fin 8,
      DyadicFinset.stencilSet c (DyadicStencil.step j) s ∈ F) :
    F.card + 1 ≤ B N := by
  exact DyadicFinset.actual_dyadic_stencil_strict_payment (Ground N) F c j (B N)
    hlegal hstar hm hcrooked hpattern

/-- The joint numerical deficit is proved from actual completion, rather
than being assumed as a reformulation of a putative counterexample. -/
theorem counterexample_joint_deficit (N : Nat) (F : Finset (Finset Int))
    (c : Int) (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N)) (hover : B N < F.card) :
    N + 1 ≤ (Avoiders F c).card + (CommonKernel (Ground N) F c).card := by
  simpa only [ground_card] using
    counterexample_forces_kernel_deficit (Ground N) F c (B N) hc hlegal hstar hover

theorem counterexample_missing_pattern (N : Nat) (F : Finset (Finset Int))
    (c : Int) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) (hover : B N < F.card) :
    ∀ j : Nat, ∃ s : Fin 8,
      DyadicFinset.stencilSet c (DyadicStencil.step j) s ∉ F := by
  exact DyadicFinset.counterexample_omits_each_dyadic_stencil
    (Ground N) F c (B N) hlegal hstar hcrooked hover

/-- The best round-20 all-N threshold, with its sole unproved extremal
dependency stated explicitly. (2*N+2)/3 is ceil(2N/3) in natural arithmetic. -/
theorem linear_omitter_threshold (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hcount : (Avoiders F c).card ≤ (2*N+2)/3) : F.card ≤ B N := by
  apply LinearThreshold.linear_omitter_bound (Ground N) F c N (B N) hc hlegal hstar
    hcrooked (ground_card N) _ hcount
  intro x hx
  exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)

/-- The actual super-B model must satisfy all three joint restrictions.
No leftover numerical budget is assumed in the theorem statement. -/
theorem counterexample_remaining_region (N : Nat) (F : Finset (Finset Int))
    (c : Int) (hc : c ∈ Ground N) (hN : 6 ≤ N)
    (hlegal : Legal (Ground N) F) (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) (hover : B N < F.card) :
    N+1 ≤ (Avoiders F c).card + (CommonKernel (Ground N) F c).card ∧
    (2*N+2)/3 + 1 ≤ (Avoiders F c).card ∧
    (CommonKernel (Ground N) F c).card ≤ N/3 := by
  have hdef := counterexample_joint_deficit N F c hc hlegal hstar hover
  have hcount : (2*N+2)/3 + 1 ≤ (Avoiders F c).card := by
    by_contra hneg
    have hbound := linear_omitter_threshold N F c hc hlegal hstar hcrooked (by omega)
    omega
  refine ⟨hdef,hcount,?_⟩
  by_contra hneg
  have hlarge : N/3 < (CommonKernel (Ground N) F c).card := by omega
  have hm : 2 ≤ (Avoiders F c).card := by omega
  have hcap := LinearThreshold.large_kernel_capacity (Ground N) F c N hc hlegal hm
    hcrooked (ground_card N)
    (by intro x hx; exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)) hN hlarge
  omega

/-- New round-22 improvement of the previously best linear threshold. -/
theorem three_quarter_omitter_threshold
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hcount : (Avoiders F c).card ≤ 3*N/4) : F.card ≤ B N := by
  apply ThreeQuarter.three_quarter_bound (Ground N) F c N (B N) hc hlegal hstar
    hcrooked (ground_card N) _ hcount
  intro x hx
  exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)

/-- Preserve the stronger old threshold at the few tiny N where ceilings
make it exceed floor(3N/4), while taking the new threshold elsewhere. -/
theorem best_omitter_threshold
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hcount : (Avoiders F c).card ≤ max ((2*N+2)/3) (3*N/4)) : F.card ≤ B N := by
  rcases le_total ((2*N+2)/3) (3*N/4) with hle | hle
  · rw [max_eq_right hle] at hcount
    exact three_quarter_omitter_threshold N F c hc hlegal hstar hcrooked hcount
  · rw [max_eq_left hle] at hcount
    exact linear_omitter_threshold N F c hc hlegal hstar hcrooked hcount

theorem counterexample_stronger_remaining_region
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) (hover : B N < F.card) :
    N+1 ≤ (Avoiders F c).card + (CommonKernel (Ground N) F c).card ∧
    N - (N-1)/4 ≤ (Avoiders F c).card ∧
    (CommonKernel (Ground N) F c).card ≤ (N-1)/4 + 1 := by
  exact ThreeQuarter.counterexample_region (Ground N) F c N (B N) hc hlegal hstar
    hcrooked (ground_card N)
    (by intro x hx; exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)) hover

/-- Round 24: the actual prime-power geometry and hereditary peeling are
fully proved; only the common-point extremum remains an explicit premise. -/
theorem five_sixths_omitter_threshold
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hcount : (Avoiders F c).card ≤ 5*N/6) : F.card ≤ B N := by
  apply FiveSixths.five_sixths_bound (Ground N) F c N (B N) hc hlegal hstar
    hcrooked (ground_card N) _ hcount
  intro x hx
  exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)

theorem best_certified_omitter_threshold
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hcount : (Avoiders F c).card ≤ max ((2*N+2)/3) (5*N/6)) : F.card ≤ B N := by
  rcases le_total ((2*N+2)/3) (5*N/6) with hle | hle
  · rw [max_eq_right hle] at hcount
    exact five_sixths_omitter_threshold N F c hc hlegal hstar hcrooked hcount
  · rw [max_eq_left hle] at hcount
    exact linear_omitter_threshold N F c hc hlegal hstar hcrooked hcount

theorem counterexample_five_sixths_remaining_region
    (N : Nat) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ground N) (hlegal : Legal (Ground N) F)
    (hstar : StarBound (Ground N) (B N))
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) (hover : B N < F.card) :
    N+1 ≤ (Avoiders F c).card + (CommonKernel (Ground N) F c).card ∧
    N - (N-1)/6 ≤ (Avoiders F c).card ∧
    (CommonKernel (Ground N) F c).card ≤ (N-1)/6 + 1 := by
  exact FiveSixths.counterexample_region (Ground N) F c N (B N) hc hlegal hstar
    hcrooked (ground_card N)
    (by intro x hx; exact Finset.mem_Icc.mpr ((mem_ground N x).mp hx)) hover

#print axioms five_sixths_omitter_threshold
#print axioms best_certified_omitter_threshold
#print axioms counterexample_five_sixths_remaining_region
#print axioms ground_card
#print axioms mem_ground
#print axioms dyadic_pattern_bound
#print axioms dyadic_pattern_strict_bound
#print axioms counterexample_joint_deficit
#print axioms counterexample_missing_pattern
#print axioms linear_omitter_threshold
#print axioms counterexample_remaining_region
#print axioms three_quarter_omitter_threshold
#print axioms best_omitter_threshold
#print axioms counterexample_stronger_remaining_region

end JSP233
