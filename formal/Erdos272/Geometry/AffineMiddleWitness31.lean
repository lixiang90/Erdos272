import Erdos272.Capacity.BudgetLoss31
import Erdos272.Capacity.QuantitativeTail31

/-! A genuine large active AP class supplies the surplus required by the
original-family payment. Existence of such a class is a separate structural
step, not assumed to follow from these conditional endpoints. -/
namespace JSP233.AffineMiddleWitness31
open StarCompletion StarResources30 CrossLine30 AffineLine30 StaircaseGeometry
open scoped Classical
noncomputable section

theorem actual_affine_pool_surplus_count (c d : ℤ) (hd : 0<d)
    (F : Finset (Finset ℤ))
    (hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet c d (Window l r) ∧ 4≤S.card)
    (hleft : ∃ S∈F, c-2*d∈S) (hright : ∃ S∈F, c+2*d∈S)
    (hcard : 1000000<F.card) :
    (F.card:ℝ)+(F.card:ℝ)/21≤(gcdStepPool c d F).card := by
  obtain ⟨U,hU,hunit⟩ := exists_normalized_family c d hd F (fun _ _ => True) (by
    intro S hS
    obtain ⟨l,r,heq,hlarge⟩ := hF S hS
    exact ⟨l,r,heq,hlarge,trivial⟩)
  have hUunit : ∀ T∈U, ∃ l r : ℕ, T=Window l r ∧ 4≤T.card := by
    intro T hT
    obtain ⟨l,r,heq,hlarge,htrue⟩ := hunit T hT
    exact ⟨l,r,heq,hlarge⟩
  have hUl : ∃ T∈U, (-2:ℤ)∈T := by
    obtain ⟨S,hS,hpoint⟩ := hleft
    have hSm : S∈mapFamily c d U := by rw [hU]; exact hS
    obtain ⟨T,hT,hmap⟩ := Finset.mem_image.mp hSm
    refine ⟨T,hT,(mem_mapSet c d hd T (-2)).mp ?_⟩
    rw [hmap]
    simpa [affine, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpoint
  have hUr : ∃ T∈U, (2:ℤ)∈T := by
    obtain ⟨S,hS,hpoint⟩ := hright
    have hSm : S∈mapFamily c d U := by rw [hU]; exact hS
    obtain ⟨T,hT,hmap⟩ := Finset.mem_image.mp hSm
    refine ⟨T,hT,(mem_mapSet c d hd T 2).mp ?_⟩
    rw [hmap]
    simpa [affine, mul_comm] using hpoint
  have hAc : F.card=U.card := by rw [←hU,mapFamily_card c d hd]
  have hPc : (gcdStepPool c d F).card=(PrimitivePool U).card := by
    rw [←hU,gcdStepPool_mapFamily_card c d hd]
  rw [hAc,hPc]
  exact QuantitativeTail31.actual_unit_family_pool_surplus_count U hUunit hUl hUr
    (by rw [←hAc]; exact hcard)

theorem actual_middle_window_of_large_active_class
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (hN : 65536≤N)
    (hc : c∈JSP233.Ground N) (hlegal : Legal (JSP233.Ground N) F)
    (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (JSP233.Ground N) F c).card≤1)
    (d : ℤ) (hactive : d∈APActiveSteps c (APLarge (RootPart F c)))
    (hlargeclass : (((N-1:ℕ):ℝ)^2/1600)≤
      ((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ)) :
    F.card<N.choose 2+1 := by
  let A := APLarge (RootPart F c)
  have hAP : ∀ S∈A, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hr : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hsz : ∀ S∈A, 4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  change d∈ActiveSteps c A (trueStep c) at hactive
  obtain ⟨hlabel,hleft,hright⟩ := Finset.mem_filter.mp hactive
  have hdpos := actual_step_labels_positive c A hAP hr d hlabel
  have hrep := actual_step_class_representation c A hAP hr hsz d
  have hn : (65535:ℝ)≤((N-1:ℕ):ℝ) := by exact_mod_cast (show 65535≤N-1 by omega)
  have hcard : 1000000<(StepClass A (trueStep c) d).card := by
    have hh : (1000000:ℝ)<((StepClass A (trueStep c) d).card:ℝ) := by
      dsimp only [A] at *
      nlinarith
    exact_mod_cast hh
  have hs := actual_affine_pool_surplus_count c d hdpos (StepClass A (trueStep c) d)
    hrep hleft hright hcard
  apply BudgetLoss31.actual_middle_window_of_line_surplus N F c hN hc hlegal hcount hkernel d hlabel
  change ((StepClass A (trueStep c) d).card:ℝ)+(((N-1:ℕ):ℝ)^2/50000)≤
    (gcdStepPool c d (StepClass A (trueStep c) d)).card
  change (((N-1:ℕ):ℝ)^2/1600)≤((StepClass A (trueStep c) d).card:ℝ) at hlargeclass
  nlinarith [sq_nonneg (((N-1:ℕ):ℝ))]

#print axioms actual_affine_pool_surplus_count
#print axioms actual_middle_window_of_large_active_class
end
end JSP233.AffineMiddleWitness31
