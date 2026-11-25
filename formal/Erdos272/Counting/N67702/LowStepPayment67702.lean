module

public import Erdos272.Counting.N67702.RootedStepTail67702
public import Erdos272.Resources.StarWindow212

@[expose] public section
namespace JSP233.StarMidpoint67702
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32 APGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Exactly the low step classes with at most a million members need an allowance.
If all available slots need that allowance, their total is bounded without using a pool. -/
theorem actual_unpaid_steps_at (m allowance : ℕ) (enough : 810000 ≤ allowance) {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hc : c ∈ Ground N) (hF : Legal (Ground N) F) :
    let A := APLarge (RootPart F c)
    let total := ∑ d ∈ LowActive m c A, ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)
    ∃ k : ℕ, k ≤ m ∧ (k = m → total ≤ (m : ℝ)*(allowance : ℝ)) ∧
      (F.card : ℝ)+(total-(k : ℝ)*(allowance : ℝ))/21 ≤
        (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
          ((N-1).choose 2 : ℕ)+((N-1 : ℕ) : ℝ)/4 := by
  let A := APLarge (RootPart F c)
  let L := LowActive m c A
  let P : Finset ℕ := L.filter (fun d:ℕ=>allowance<(StepClass A (trueStep c) (d:ℤ)).card)
  let D := P.image (fun d:ℕ=>(d:ℤ))
  have hAP : ∀S∈A,IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀S∈A,4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have hground : ∀S∈A,S⊆Ground N := fun S hS =>
    hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hD : D⊆APActiveSteps c A := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1
  have hbig : ∀d∈D,allowance<(StepClass A (trueStep c) d).card := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp he).2
  have hb := StarWindow212.actual_budget_with_small_surpluses hc hF D hD
    (fun d hd => lt_of_le_of_lt enough (hbig d hd))
  have hsumD : (∑d∈D,((StepClass A (trueStep c) d).card:ℝ))=
      ∑d∈P,((StepClass A (trueStep c) (d:ℤ)).card:ℝ) := by
    dsimp only [D]
    rw [Finset.sum_image]
    intro i _ j _ hij
    change (i:ℤ)=(j:ℤ) at hij
    exact_mod_cast hij
  have hsub : L⊆Finset.Icc 1 m := by
    intro d hd
    have hdata := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (nat_labels_bound N c A hground hAP hroot hlarge hdata.1)).1,
       hdata.2.2⟩
  have hcard : L.card≤m := by simpa using Finset.card_le_card hsub
  have sub : P ⊆ L := Finset.filter_subset _ _
  let small := L \ P
  have counts : small.card + P.card = L.card := Finset.card_sdiff_add_card_eq_card sub
  have unpaid : (∑ d ∈ small, ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)) ≤
      (small.card : ℝ)*(allowance : ℝ) := calc
    _ ≤ ∑ _d ∈ small, (allowance : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hL,hn⟩ := Finset.mem_sdiff.mp hd
      have le : (StepClass A (trueStep c) (d : ℤ)).card ≤ allowance := by
        by_contra! gt
        exact hn (Finset.mem_filter.mpr ⟨hL,gt⟩)
      exact_mod_cast le
    _ = _ := by simp
  let size (d : ℕ) : ℝ := (StepClass A (trueStep c) (d : ℤ)).card
  have part : (∑ d ∈ small, size d)+(∑ d ∈ P, size d)=∑ d ∈ L, size d :=
    Finset.sum_sdiff sub
  change (∑ d ∈ small, size d) ≤ (small.card : ℝ)*(allowance : ℝ) at unpaid
  change (F.card : ℝ)+(∑ d ∈ D, ((StepClass A (trueStep c) d).card : ℝ))/21 ≤ _ at hb
  rw [hsumD] at hb
  change (F.card : ℝ)+(∑ d ∈ P, size d)/21 ≤ _ at hb
  refine ⟨small.card, by omega, ?_, ?_⟩
  · intro full
    have empty : P = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [empty,Finset.sum_empty,add_zero] at part
    change (∑ d ∈ L, size d) ≤ (m : ℝ)*(allowance : ℝ)
    rwa [←part,←full]
  · change (F.card : ℝ)+((∑ d ∈ L, size d)-(small.card : ℝ)*(allowance : ℝ))/21 ≤ _
    linarith only [unpaid,part,hb]

theorem actual_unpaid_steps (m : ℕ) {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hc : c ∈ Ground N) (hF : Legal (Ground N) F) :
    let A := APLarge (RootPart F c)
    let total := ∑ d ∈ LowActive m c A, ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)
    ∃ k : ℕ, k ≤ m ∧ (k = m → total ≤ (m : ℝ)*1000000) ∧
      (F.card : ℝ)+(total-(k : ℝ)*1000000)/21 ≤
        (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
          ((N-1).choose 2 : ℕ)+((N-1 : ℕ) : ℝ)/4 :=
  actual_unpaid_steps_at m 1000000 (by decide) hc hF

#print axioms actual_unpaid_steps
end
end JSP233.StarMidpoint67702
