module

public import Erdos272.Capacity.N20258.RootHeight20258
public import Erdos272.Counting.N67702.RootedStepTail67702
public import Erdos272.Counting.APCount41

@[expose] public section
namespace JSP233.RootHeightBudget20258
open StarCompletion StarResources30 CrossLine30 JointResources31 AffineLine30
open LowSteps32 RootHeight20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Sum a signed credit over a selection of genuine step classes. The
unselected classes use the original one-pair budget. -/
private theorem sum_credits {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hc : c ∈ Ground N) (legal : Legal (Ground N) F)
    (D : Finset ℤ) (credit : ℤ → ℝ)
    (active : D ⊆ APActiveSteps c (APLarge (RootPart F c)))
    (paid : ∀ d ∈ D, let U := StepClass (APLarge (RootPart F c)) (trueStep c) d
      (U.card : ℝ)+credit d ≤ (gcdStepPool c d U).card) :
    (F.card : ℝ)+∑ d ∈ D, credit d ≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
      ((N-1).choose 2 : ℕ)+((N-1 : ℕ) : ℝ)/4 := by
  let A := APLarge (RootPart F c)
  have ap : ∀ S ∈ A, IsAP S := fun _ hs => (Finset.mem_filter.mp hs).2.1
  have root : Rooted A c := fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have large : ∀ S ∈ A, 4 ≤ S.card := fun _ hs => (Finset.mem_filter.mp hs).2.2
  have labels : D ⊆ StepLabels A (trueStep c) := fun _ hd => (Finset.mem_filter.mp (active hd)).1
  have each (d : ℤ) (hd : d ∈ StepLabels A (trueStep c)) :
      ((StepClass A (trueStep c) d).card : ℝ)+(if d ∈ D then credit d else 0) ≤
      (gcdStepPool c d (StepClass A (trueStep c) d)).card+
        (if d ∈ APActiveSteps c A then (1 : ℝ) else 0) := by
    by_cases sel : d ∈ D
    · rw [ite_eq_left sel,ite_eq_left (active sel)]
      have p := paid d sel
      change ((StepClass A (trueStep c) d).card : ℝ)+credit d ≤ _ at p
      linarith only [p]
    · rw [ite_eq_right sel,add_zero]
      exact_mod_cast actual_step_class_count c A ap root large d hd
  have all := Finset.sum_le_sum each
  have filter : (StepLabels A (trueStep c)).filter (fun d => d ∈ D)=D := by
    ext d
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hd => labels hd)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_filter,filter] at all
  have a : (∑ d ∈ StepLabels A (trueStep c), ((StepClass A (trueStep c) d).card : ℝ))=A.card := by
    exact_mod_cast sum_stepClass_card A (trueStep c)
  have p : (∑ d ∈ StepLabels A (trueStep c),
      ((gcdStepPool c d (StepClass A (trueStep c) d)).card : ℝ))=(APResourcePool c A).card := by
    exact_mod_cast sum_stepPool_card c A (trueStep c) (actual_step_labels_positive c A ap root)
  have act : (∑ d ∈ StepLabels A (trueStep c),
      if d ∈ APActiveSteps c A then (1 : ℝ) else 0)=(APActiveSteps c A).card := by
    exact_mod_cast sum_active_indicator c A (trueStep c)
  rw [a,p,act] at all
  have raw := BudgetLoss31.actual_one_private_budget c (Ground N) F hc legal
  rw [ground_card] at raw
  have rawR : (F.card : ℝ)+(APResourcePool c A).card ≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+((N-1).choose 2 : ℕ)+(A.card : ℝ) := by
    exact_mod_cast raw
  have small := BudgetLoss31.actual_active_card_le N F c legal
  have four : 4*(APActiveSteps c A).card ≤ N-1 := by
    change (APActiveSteps c A).card ≤ (N-1)/4 at small
    omega
  have fourR : 4*((APActiveSteps c A).card : ℝ) ≤ (N-1 : ℕ) := by exact_mod_cast four
  linarith only [all,rawR,fourR]

def debt (x : ℝ) : ℝ :=
  quadratic*(5/3)*x^2+linear*(7493/1600)*x+60*constant

private theorem sum_debt {L : Finset ℕ} {x : ℝ}
    (sub : L ⊆ Finset.Icc 1 60) (pos : 0 ≤ x) :
    (∑ d ∈ L, (quadratic*(x/d)^2+linear*(x/d)+constant)) ≤ debt x := by
  have nonneg (d : ℕ) : 0 ≤ quadratic*(x/d)^2+linear*(x/d)+constant := by
    unfold quadratic linear constant
    positivity
  have all := Finset.sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => nonneg d)
  have eq (d : ℕ) : quadratic*(x/d)^2+linear*(x/d)+constant =
      (quadratic*x^2)*((1 : ℝ)/(d : ℝ)^2)+(linear*x)*(1/(d : ℝ))+constant := by ring
  simp_rw [eq,Finset.sum_add_distrib,←Finset.mul_sum] at all
  have square := APCount41.square_reciprocal_bound 60
  unfold APCount41.SquareReciprocal at square
  have h := harmonic_sixty
  unfold HarmonicAbel29.Harmonic at h
  have qs := mul_le_mul_of_nonneg_left square (show 0 ≤ quadratic*x^2 by unfold quadratic; positivity)
  have ls := mul_le_mul_of_nonneg_left h (show 0 ≤ linear*x by unfold linear; positivity)
  have count : (Finset.Icc 1 60 : Finset ℕ).card=60 := by decide
  simp only [Finset.sum_const,nsmul_eq_mul,count,Nat.cast_ofNat] at all
  unfold debt
  simp_rw [eq,Finset.sum_add_distrib,←Finset.mul_sum]
  simp only [Finset.sum_const,nsmul_eq_mul]
  linarith only [all,qs,ls]

/-- The same root pays all active classes of spacing at most 60, with one
height term for the whole family. -/
theorem actual_budget {N c : ℕ} {F : Finset (Finset ℤ)}
    (hc : (c : ℤ) ∈ Ground N) (legal : Legal (Ground N) F) :
    let A := APLarge (RootPart F (c : ℤ))
    let L := StarMidpoint67702.LowActive 60 (c : ℤ) A
    (F.card : ℝ)+(∑ d ∈ L, ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)) ≤
      (Avoiders F (c : ℤ)).card+(CommonKernel (Ground N) F (c : ℤ)).card+
      ((N-1).choose 2 : ℕ)+((N-1 : ℕ) : ℝ)/4+debt ((c : ℝ)-1) := by
  let A := APLarge (RootPart F (c : ℤ))
  let L := StarMidpoint67702.LowActive 60 (c : ℤ) A
  let D := L.image (fun d : ℕ => (d : ℤ))
  let x : ℝ := (c : ℝ)-1
  let cost (d : ℕ) : ℝ := quadratic*(x/d)^2+linear*(x/d)+constant
  let size (d : ℤ) : ℝ := (StepClass A (trueStep c) d).card
  let credit (d : ℤ) := size d-cost d.toNat
  have ground : ∀ S ∈ A, S ⊆ Ground N := fun S hs =>
    legal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have ap : ∀ S ∈ A, IsAP S := fun _ hs => (Finset.mem_filter.mp hs).2.1
  have root : Rooted A (c : ℤ) := fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have large : ∀ S ∈ A, 4 ≤ S.card := fun _ hs => (Finset.mem_filter.mp hs).2.2
  have active (d : ℕ) (hd : d ∈ L) : (d : ℤ) ∈ APActiveSteps (c : ℤ) A :=
    (Finset.mem_filter.mp hd).2.1
  have sub : L ⊆ Finset.Icc 1 60 := by
    intro d hd
    have mem := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp
      (nat_labels_bound N (c : ℤ) A ground ap root large mem.1)).1,mem.2.2⟩
  have budget := sum_credits hc legal D credit (by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    exact active i hi) (by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    have dz : 0 < i := (Finset.mem_Icc.mp (sub hi)).1
    have p := actual_class hc dz ground ap root large (active i hi)
    change 2*size (i : ℤ) ≤ _+quadratic*(x/i)^2+linear*(x/i)+constant at p
    change size (i : ℤ)+(size (i : ℤ)-cost (i : ℤ).toNat) ≤ _
    rw [Int.toNat_natCast]
    dsimp only [cost]
    linarith only [p])
  have sum : (∑ d ∈ D, credit d) =
      (∑ d ∈ L, size (d : ℤ))-(∑ d ∈ L, cost d) := by
    dsimp only [D]
    rw [Finset.sum_image (fun i _ j _ h => (Int.ofNat_inj.mp h))]
    simp only [credit,Int.toNat_natCast,Finset.sum_sub_distrib]
  rw [sum] at budget
  have one : 1 ≤ c := by exact_mod_cast ((mem_ground N _).mp hc).1
  have oneR : (1 : ℝ) ≤ c := by exact_mod_cast one
  have costs := sum_debt sub (show 0 ≤ x by dsimp [x]; linarith only [oneR])
  change (∑ d ∈ L, cost d) ≤ debt x at costs
  change (F.card : ℝ)+(∑ d ∈ L, size (d : ℤ)) ≤ _
  linarith only [budget,costs]

#print axioms actual_budget
end
end JSP233.RootHeightBudget20258
