import Erdos272.Resources.JointResources31
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual one-private-pair root accounting, retaining a quantitative loss on
one actual AP step class. The final payment accepts that geometric surplus
as an explicit witness and does not assume the desired original-family bound. -/
namespace JSP233.BudgetLoss31
open StarCompletion StarResources30 CrossLine30 JointResources31
open scoped Classical BigOperators
noncomputable section

theorem actual_one_private_budget (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hc : c∈Ω) (hlegal : Legal Ω F) :
    F.card+(APResourcePool c (APLarge (RootPart F c))).card ≤
      (Avoiders F c).card+(CommonKernel Ω F c).card+(Ω.card-1).choose 2+
        (APLarge (RootPart F c)).card := by
  let G := RootPart F c
  have hG := rootPart_legal c Ω F hlegal
  have hr := rootPart_rooted c F
  have hp := family_partition G
  have hs := root_small_card_le_kernel c Ω F hlegal
  have hu := three_resource_pools_card_le c Ω G hG hr
  have hz := PrivatePairExistence.crooked_members_card_le_available_pairs_at_root hG hr
  have ha := Finset.card_le_card (actual_AP_pool_subset_covered c Ω G hG.1)
  have hf := root_avoider_card_partition F c
  have he : (PairUniverse c Ω).card=(Ω.card-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem hc]
  rw [he] at hu
  dsimp only [G] at hp hu hz ha
  linarith only [hp,hs,hu,hz,ha,hf]

theorem one_class_surplus (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S∈F, IsAP S) (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card)
    (d : ℤ) (hd : d∈StepLabels F (trueStep c)) (loss : ℝ)
    (hsurplus : ((StepClass F (trueStep c) d).card:ℝ)+loss ≤
      (AffineLine30.gcdStepPool c d (StepClass F (trueStep c) d)).card) :
    (F.card:ℝ)+loss ≤ (APResourcePool c F).card+(APActiveSteps c F).card := by
  have hpoint : ∀ e∈StepLabels F (trueStep c),
      ((StepClass F (trueStep c) e).card:ℝ)+(if e=d then loss else 0) ≤
        (AffineLine30.gcdStepPool c e (StepClass F (trueStep c) e)).card+
          (if e∈ActiveSteps c F (trueStep c) then (1:ℝ) else 0) := by
    intro e he
    by_cases hed : e=d
    · subst e
      rw [if_pos rfl]
      have hi : (0:ℝ) ≤ (if d∈ActiveSteps c F (trueStep c) then 1 else 0) := by
        split_ifs <;> norm_num
      linarith
    · rw [if_neg hed,add_zero]
      have hh := actual_step_class_count c F hAP hroot hlarge e he
      exact_mod_cast hh
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hh
  have hD : (∑ e∈StepLabels F (trueStep c), if e=d then loss else 0)=loss := by
    simp [hd]
  rw [hD] at hh
  have hA : (∑ e∈StepLabels F (trueStep c), ((StepClass F (trueStep c) e).card:ℝ))=F.card := by
    exact_mod_cast sum_stepClass_card F (trueStep c)
  have hP : (∑ e∈StepLabels F (trueStep c),
      ((AffineLine30.gcdStepPool c e (StepClass F (trueStep c) e)).card:ℝ))=
        (APResourcePool c F).card := by
    exact_mod_cast sum_stepPool_card c F (trueStep c)
      (actual_step_labels_positive c F hAP hroot)
  have hI : (∑ e∈StepLabels F (trueStep c),
      if e∈ActiveSteps c F (trueStep c) then (1:ℝ) else 0)=(APActiveSteps c F).card := by
    exact_mod_cast sum_active_indicator c F (trueStep c)
  rwa [hA,hP,hI] at hh

theorem actual_budget_with_line_surplus (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hc : c∈Ω) (hlegal : Legal Ω F)
    (d : ℤ) (hd : d∈StepLabels (APLarge (RootPart F c)) (trueStep c)) (loss : ℝ)
    (hsurplus : ((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ)+loss ≤
      (AffineLine30.gcdStepPool c d (StepClass (APLarge (RootPart F c)) (trueStep c) d)).card) :
    (F.card:ℝ)+loss ≤ (Avoiders F c).card+(CommonKernel Ω F c).card+
      ((Ω.card-1).choose 2:ℕ)+(APActiveSteps c (APLarge (RootPart F c))).card := by
  have hbase := actual_one_private_budget c Ω F hc hlegal
  have hbr : (F.card:ℝ)+(APResourcePool c (APLarge (RootPart F c))).card ≤
      (Avoiders F c).card+(CommonKernel Ω F c).card+((Ω.card-1).choose 2:ℕ)+
        (APLarge (RootPart F c)).card := by exact_mod_cast hbase
  have hl := one_class_surplus c (APLarge (RootPart F c))
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2)
    (fun S hS => (Finset.mem_filter.mp hS).2.2) d hd loss hsurplus
  linarith

theorem actual_active_card_le (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hlegal : Legal (Ground N) F) :
    (APActiveSteps c (APLarge (RootPart F c))).card≤(N-1)/4 := by
  apply StarBudget30.active_steps_card_le N c
  intro d hd
  have hG := rootPart_legal c (Ground N) F hlegal
  obtain ⟨hp,hL,hR⟩ := actual_APLarge_active_geometry c (Ground N) (RootPart F c)
    hG.1 (rootPart_rooted c F) hd
  exact ⟨hp,((mem_ground N _).mp hL).1,((mem_ground N _).mp hR).2⟩

theorem physical_budget_with_line_surplus (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (d : ℤ) (hd : d∈StepLabels (APLarge (RootPart F c)) (trueStep c)) (loss : ℝ)
    (hsurplus : ((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ)+loss ≤
      (AffineLine30.gcdStepPool c d (StepClass (APLarge (RootPart F c)) (trueStep c) d)).card) :
    (F.card:ℝ)+loss ≤ (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
      ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 := by
  have hh := actual_budget_with_line_surplus c (Ground N) F hc hlegal d hd loss hsurplus
  rw [ground_card] at hh
  have ha := actual_active_card_le N F c hlegal
  have hf : 4*((N-1)/4)≤N-1 := by omega
  have har : ((APActiveSteps c (APLarge (RootPart F c))).card:ℝ)≤((N-1:ℕ):ℝ)/4 := by
    have h1 : ((APActiveSteps c (APLarge (RootPart F c))).card:ℝ)≤((N-1)/4:ℕ) := by exact_mod_cast ha
    have h2 : (4:ℝ)*((N-1)/4:ℕ)≤((N-1:ℕ):ℝ) := by exact_mod_cast hf
    linarith
  linarith

theorem middle_window_numeric_payment (n h k f pairs : ℝ)
    (hn : 65535≤n) (hh : h≤2*n-4) (hk : k≤1)
    (hbudget : f+n^2/50000≤h+k+pairs+n/4) : f<pairs+n+1 := by
  have hquad : 0<n^2-62500*n+200000 := by
    have hfac : 0≤(n-65535)*(n+65535-62500) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  nlinarith

theorem actual_middle_window_of_line_surplus
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (hN : 65536≤N)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (d : ℤ) (hd : d∈StepLabels (APLarge (RootPart F c)) (trueStep c))
    (hsurplus : ((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ)+
        (((N-1:ℕ):ℝ)^2/50000) ≤
      (AffineLine30.gcdStepPool c d (StepClass (APLarge (RootPart F c)) (trueStep c) d)).card) :
    F.card<N.choose 2+1 := by
  have hh := physical_budget_with_line_surplus N F c hc hlegal d hd _ hsurplus
  have hn : (65535:ℝ)≤((N-1:ℕ):ℝ) := by exact_mod_cast (show 65535≤N-1 by omega)
  have hhc : ((Avoiders F c).card:ℝ)≤2*((N-1:ℕ):ℝ)-4 := by
    have h4 : ((Avoiders F c).card:ℝ)+4≤2*((N-1:ℕ):ℝ) := by
      exact_mod_cast (show (Avoiders F c).card+4≤2*(N-1) by omega)
    linarith
  have hkc : ((CommonKernel (Ground N) F c).card:ℝ)≤1 := by exact_mod_cast hkernel
  have hfin := middle_window_numeric_payment ((N-1:ℕ):ℝ)
    (Avoiders F c).card (CommonKernel (Ground N) F c).card F.card ((N-1).choose 2)
    hn hhc hkc hh
  have hNc : (N:ℝ)=((N-1:ℕ):ℝ)+1 := by
    exact_mod_cast (show N=(N-1)+1 by omega)
  have hid := StarBudget30.small_budget_identity N (by omega)
  rw [←hid]
  have hf : (F.card:ℝ)<(N:ℝ)+((N-1).choose 2:ℕ) := by linarith
  exact_mod_cast hf

#print axioms actual_one_private_budget
#print axioms one_class_surplus
#print axioms actual_budget_with_line_surplus
#print axioms actual_active_card_le
#print axioms physical_budget_with_line_surplus
#print axioms middle_window_numeric_payment
#print axioms actual_middle_window_of_line_surplus
end
end JSP233.BudgetLoss31
