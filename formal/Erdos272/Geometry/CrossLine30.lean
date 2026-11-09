module

public import Erdos272.Geometry.AffineLine30
public import Erdos272.Resources.StarResources30
public import Erdos272.Foundation.PrivatePairExistence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! Actual gcd-labelled line pools. Distinct positive steps use disjoint
physical two-point resources. The linewise defects are summed only over
active lines, with the thin-line estimates paying no dummy. -/
namespace JSP233.CrossLine30
open StarCompletion PrivatePairExistence StaircaseGeometry AffineLine30
open scoped BigOperators

theorem primitive_step_unique {c d e : ℤ} {Q : Finset ℤ}
    (hd : 0 < d) (he : 0 < e)
    (hQd : IsStepPrimitive c d Q) (hQe : IsStepPrimitive c e Q) : d = e := by
  obtain ⟨u,v,huv,hrep⟩ := Finset.card_eq_two.mp hQd.1
  have hu : u ∈ Q := by simp [hrep]
  have hv : v ∈ Q := by simp [hrep]
  have hnat : d.natAbs = e.natAbs :=
    (hQd.2.2.2 u hu v hv huv).symm.trans (hQe.2.2.2 u hu v hv huv)
  have hdcast : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd.le
  have hecast : (e.natAbs : ℤ) = e := Int.natAbs_of_nonneg he.le
  exact hdcast.symm.trans ((congrArg Int.ofNat hnat).trans hecast)

theorem step_pools_disjoint (c d e : ℤ) (F G : Finset (Finset ℤ))
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    Disjoint (gcdStepPool c d F) (gcdStepPool c e G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hQd hQe
  obtain ⟨S,hS,hsub,hprim⟩ := (mem_gcdStepPool c d F Q).mp hQd
  obtain ⟨T,hT,hsub',hprim'⟩ := (mem_gcdStepPool c e G Q).mp hQe
  exact hne (primitive_step_unique hd he hprim hprim')

theorem available_disjoint_step_pool (c d : ℤ) (Ω : Finset ℤ)
    (F G : Finset (Finset ℤ)) (hGF : G ⊆ F)
    (hAP : ∀ S ∈ G, IsAP S) :
    Disjoint (AvailableBadPairsAt c Ω F) (gcdStepPool c d G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hQA hQP
  have hprivate := (Finset.mem_filter.mp hQA).2.2.2.2
  obtain ⟨S,hSG,hsub,hprim⟩ := (mem_gcdStepPool c d G Q).mp hQP
  exact hprivate S (hGF hSG) (hAP S hSG) hsub

noncomputable def StepLabels (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) : Finset ℤ :=
  F.image step

noncomputable def StepClass (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) (d : ℤ) :
    Finset (Finset ℤ) := by
  classical
  exact F.filter (fun S => step S = d)

noncomputable def AllStepPool (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) :
    Finset (Finset ℤ) :=
  (StepLabels F step).biUnion (fun d => gcdStepPool c d (StepClass F step d))

noncomputable def ActiveSteps (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) :
    Finset ℤ := by
  classical
  exact (StepLabels F step).filter (fun d =>
    (∃ S ∈ StepClass F step d, c - 2*d ∈ S) ∧
    (∃ S ∈ StepClass F step d, c + 2*d ∈ S))

theorem stepClass_subset (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) (d : ℤ) :
    StepClass F step d ⊆ F := Finset.filter_subset _ _

theorem sum_stepClass_card (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) :
    (∑ d ∈ StepLabels F step, (StepClass F step d).card) = F.card := by
  classical
  have hfilter : F.filter (fun S => step S ∈ F.image step) = F := by
    apply Finset.filter_true_of_mem
    intro S hS
    exact Finset.mem_image.mpr ⟨S,hS,rfl⟩
  have hh := Finset.sum_card_fiberwise_eq_card_filter F (F.image step) step
  rw [hfilter] at hh
  exact hh

theorem sum_stepPool_card (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ)
    (hpos : ∀ d ∈ StepLabels F step, 0 < d) :
    (∑ d ∈ StepLabels F step, (gcdStepPool c d (StepClass F step d)).card) =
      (AllStepPool c F step).card := by
  classical
  symm
  apply Finset.card_biUnion
  intro d hd e he hne
  exact step_pools_disjoint c d e _ _ (hpos d hd) (hpos e he) hne

theorem sum_active_indicator (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) :
    (∑ d ∈ StepLabels F step, if d ∈ ActiveSteps c F step then 1 else 0) =
      (ActiveSteps c F step).card := by
  classical
  rw [Finset.sum_boole]
  have heq : (StepLabels F step).filter (fun d => d ∈ ActiveSteps c F step) =
      ActiveSteps c F step := by
    ext d
    simp [ActiveSteps]
  exact congrArg Finset.card heq

theorem sum_linewise_count (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ)
    (hpos : ∀ d ∈ StepLabels F step, 0 < d)
    (hline : ∀ d ∈ StepLabels F step,
      (StepClass F step d).card ≤ (gcdStepPool c d (StepClass F step d)).card +
        if d ∈ ActiveSteps c F step then 1 else 0) :
    F.card ≤ (AllStepPool c F step).card + (ActiveSteps c F step).card := by
  classical
  have hs := Finset.sum_le_sum hline
  simpa only [Finset.sum_add_distrib, sum_stepClass_card, sum_stepPool_card c F step hpos,
    sum_active_indicator] using hs

theorem all_pool_members (c : ℤ) (F : Finset (Finset ℤ)) (step : Finset ℤ → ℤ)
    {Q : Finset ℤ} (hQ : Q ∈ AllStepPool c F step) :
    Q.card = 2 ∧ c ∉ Q ∧ ¬IsAP (insert c Q) ∧ ∃ S ∈ F, Q ⊆ S := by
  obtain ⟨d,hd,hQP⟩ := Finset.mem_biUnion.mp hQ
  obtain ⟨S,hS,hsub,hprim⟩ := (mem_gcdStepPool c d (StepClass F step d) Q).mp hQP
  exact ⟨hprim.1,hprim.2.1,hprim.2.2.1,S,stepClass_subset F step d hS,hsub⟩

theorem available_disjoint_all_pool (c : ℤ) (Ω : Finset ℤ)
    (F G : Finset (Finset ℤ)) (step : Finset ℤ → ℤ) (hGF : G ⊆ F)
    (hAP : ∀ S ∈ G, IsAP S) :
    Disjoint (AvailableBadPairsAt c Ω F) (AllStepPool c G step) := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hQA hQP
  have hprivate := (Finset.mem_filter.mp hQA).2.2.2.2
  obtain ⟨hcard,hc,hbad,S,hS,hsub⟩ := all_pool_members c G step hQP
  exact hprivate S (hGF hS) (hAP S hS) hsub

noncomputable def trueStep (c : ℤ) (S : Finset ℤ) : ℤ := by
  classical
  exact if h : IsAP S ∧ c ∈ S then
    Classical.choose (actual_AP_representation h.1 h.2) else 1

theorem trueStep_representation {c : ℤ} {S : Finset ℤ}
    (hAP : IsAP S) (hc : c ∈ S) :
    0 < trueStep c S ∧ ∃ l r : ℕ, S = mapSet c (trueStep c S) (Window l r) := by
  classical
  unfold trueStep
  rw [dif_pos ⟨hAP,hc⟩]
  exact Classical.choose_spec (actual_AP_representation hAP hc)

theorem trueStep_eq_of_representation {c d : ℤ} {S : Finset ℤ} {l r : ℕ}
    (hAP : IsAP S) (hc : c ∈ S) (hcard : 2 ≤ S.card) (hd : 0 < d)
    (hrep : S = mapSet c d (Window l r)) : trueStep c S = d := by
  obtain ⟨hp,L,R,hrep'⟩ := trueStep_representation hAP hc
  exact step_unique hp hd hcard hrep' hrep

theorem actual_step_labels_positive (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c) :
    ∀ d ∈ StepLabels F (trueStep c), 0 < d := by
  intro d hd
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hd
  exact (trueStep_representation (hAP S hS) (hroot S hS)).1

theorem actual_step_class_representation (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c)
    (hlarge : ∀ S ∈ F, 4 ≤ S.card) (d : ℤ) :
    ∀ S ∈ StepClass F (trueStep c) d,
      ∃ l r : ℕ, S = mapSet c d (Window l r) ∧ 4 ≤ S.card := by
  intro S hS
  have hSF := (Finset.mem_filter.mp hS).1
  have hstep := (Finset.mem_filter.mp hS).2
  obtain ⟨hp,l,r,hrep⟩ := trueStep_representation (hAP S hSF) (hroot S hSF)
  exact ⟨l,r,by simpa [hstep] using hrep,hlarge S hSF⟩

theorem mapWindow_neg_two_mem (c d : ℤ) (l r : ℕ) (hl : 2 ≤ l) :
    c - 2*d ∈ mapSet c d (Window l r) := by
  apply Finset.mem_image.mpr
  refine ⟨-2,?_,?_⟩
  · rw [mem_window]
    constructor <;> omega
  · dsimp [affine]
    ring

theorem mapWindow_pos_two_mem (c d : ℤ) (l r : ℕ) (hr : 2 ≤ r) :
    c + 2*d ∈ mapSet c d (Window l r) := by
  apply Finset.mem_image.mpr
  refine ⟨2,?_,?_⟩
  · rw [mem_window]
    constructor <;> omega
  · dsimp [affine]
    ring

noncomputable def APResourcePool (c : ℤ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  AllStepPool c F (trueStep c)

noncomputable def APActiveSteps (c : ℤ) (F : Finset (Finset ℤ)) : Finset ℤ :=
  ActiveSteps c F (trueStep c)

theorem active_step_geometry (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c)
    (hground : ∀ S ∈ F, S ⊆ Ω) {d : ℤ} (hd : d ∈ APActiveSteps c F) :
    0 < d ∧ c - 2*d ∈ Ω ∧ c + 2*d ∈ Ω := by
  have hdlabel := (Finset.mem_filter.mp hd).1
  have hdactive := (Finset.mem_filter.mp hd).2
  obtain ⟨S,hS,hleft⟩ := hdactive.1
  obtain ⟨T,hT,hright⟩ := hdactive.2
  exact ⟨actual_step_labels_positive c F hAP hroot d hdlabel,
    hground S (stepClass_subset F (trueStep c) d hS) hleft,
    hground T (stepClass_subset F (trueStep c) d hT) hright⟩

theorem actual_AP_pool_subset_covered (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S ∈ F, S ⊆ Ω) :
    APResourcePool c (StarResources30.APLarge F) ⊆
      StarResources30.CoveredAPBadPairs c Ω F := by
  classical
  intro Q hQ
  obtain ⟨hcard,hc,hbad,S,hS,hsub⟩ :=
    all_pool_members c (StarResources30.APLarge F) (trueStep c) hQ
  have hSF := (Finset.mem_filter.mp hS).1
  have hAPS := (Finset.mem_filter.mp hS).2.1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (hsub.trans (hground S hSF)),
    hcard,hc,hbad,S,hSF,hAPS,hsub⟩

theorem inactive_step_class_count (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c)
    (hlarge : ∀ S ∈ F, 4 ≤ S.card) {d : ℤ}
    (hd : d ∈ StepLabels F (trueStep c))
    (hinactive : d ∉ ActiveSteps c F (trueStep c)) :
    (StepClass F (trueStep c) d).card ≤
      (gcdStepPool c d (StepClass F (trueStep c) d)).card := by
  classical
  have hdpos := actual_step_labels_positive c F hAP hroot d hd
  have hrep := actual_step_class_representation c F hAP hroot hlarge d
  by_cases hleft : ∃ S ∈ StepClass F (trueStep c) d, c - 2*d ∈ S
  · have hnright : ¬∃ S ∈ StepClass F (trueStep c) d, c + 2*d ∈ S := by
      intro hright
      exact hinactive (Finset.mem_filter.mpr ⟨hd,hleft,hright⟩)
    have hthin : ∀ S ∈ StepClass F (trueStep c) d,
        ∃ l r : ℕ, S = mapSet c d (Window l r) ∧ 4 ≤ S.card ∧ r ≤ 1 := by
      intro S hS
      obtain ⟨l,r,hSrep,hScard⟩ := hrep S hS
      refine ⟨l,r,hSrep,hScard,?_⟩
      by_contra hr
      apply hnright
      refine ⟨S,hS,?_⟩
      rw [hSrep]
      exact mapWindow_pos_two_mem c d l r (by omega)
    have hh := fixed_step_right_thin_defect_nonpos c d hdpos
      (StepClass F (trueStep c) d) hthin
    omega
  · have hthin : ∀ S ∈ StepClass F (trueStep c) d,
        ∃ l r : ℕ, S = mapSet c d (Window l r) ∧ 4 ≤ S.card ∧ l ≤ 1 := by
      intro S hS
      obtain ⟨l,r,hSrep,hScard⟩ := hrep S hS
      refine ⟨l,r,hSrep,hScard,?_⟩
      by_contra hl
      apply hleft
      refine ⟨S,hS,?_⟩
      rw [hSrep]
      exact mapWindow_neg_two_mem c d l r (by omega)
    have hh := fixed_step_left_thin_defect_nonpos c d hdpos
      (StepClass F (trueStep c) d) hthin
    omega

theorem actual_step_class_count (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c)
    (hlarge : ∀ S ∈ F, 4 ≤ S.card) :
    ∀ d ∈ StepLabels F (trueStep c),
      (StepClass F (trueStep c) d).card ≤
        (gcdStepPool c d (StepClass F (trueStep c) d)).card +
          if d ∈ ActiveSteps c F (trueStep c) then 1 else 0 := by
  classical
  intro d hd
  by_cases hactive : d ∈ ActiveSteps c F (trueStep c)
  · rw [if_pos hactive]
    have hh := fixed_step_defect_le_one c d
      (actual_step_labels_positive c F hAP hroot d hd)
      (StepClass F (trueStep c) d)
      (actual_step_class_representation c F hAP hroot hlarge d)
    omega
  · rw [if_neg hactive, Nat.add_zero]
    exact inactive_step_class_count c F hAP hroot hlarge hd hactive

theorem actual_AP_family_count (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S ∈ F, IsAP S) (hroot : Rooted F c)
    (hlarge : ∀ S ∈ F, 4 ≤ S.card) :
    F.card ≤ (APResourcePool c F).card + (APActiveSteps c F).card := by
  exact sum_linewise_count c F (trueStep c)
    (actual_step_labels_positive c F hAP hroot)
    (actual_step_class_count c F hAP hroot hlarge)

theorem actual_APLarge_count_le_covered (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hground : ∀ S ∈ F, S ⊆ Ω) (hroot : Rooted F c) :
    (StarResources30.APLarge F).card ≤
      (StarResources30.CoveredAPBadPairs c Ω F).card +
        (APActiveSteps c (StarResources30.APLarge F)).card := by
  classical
  have hh := actual_AP_family_count c (StarResources30.APLarge F)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  exact hh.trans (Nat.add_le_add_right
    (Finset.card_le_card (actual_AP_pool_subset_covered c Ω F hground)) _)

theorem actual_APLarge_active_geometry (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hground : ∀ S ∈ F, S ⊆ Ω) (hroot : Rooted F c)
    {d : ℤ} (hd : d ∈ APActiveSteps c (StarResources30.APLarge F)) :
    0 < d ∧ c - 2*d ∈ Ω ∧ c + 2*d ∈ Ω := by
  classical
  exact active_step_geometry c Ω (StarResources30.APLarge F)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS => hground S (Finset.mem_filter.mp hS).1) hd

#print axioms primitive_step_unique
#print axioms step_pools_disjoint
#print axioms available_disjoint_step_pool
#print axioms stepClass_subset
#print axioms sum_stepClass_card
#print axioms sum_stepPool_card
#print axioms sum_active_indicator
#print axioms sum_linewise_count
#print axioms all_pool_members
#print axioms available_disjoint_all_pool
#print axioms trueStep_representation
#print axioms trueStep_eq_of_representation
#print axioms actual_step_labels_positive
#print axioms actual_step_class_representation
#print axioms mapWindow_neg_two_mem
#print axioms mapWindow_pos_two_mem
#print axioms active_step_geometry
#print axioms actual_AP_pool_subset_covered
#print axioms inactive_step_class_count
#print axioms actual_step_class_count
#print axioms actual_AP_family_count
#print axioms actual_APLarge_count_le_covered
#print axioms actual_APLarge_active_geometry

end JSP233.CrossLine30
