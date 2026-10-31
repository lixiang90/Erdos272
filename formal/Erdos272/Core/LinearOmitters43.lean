import Erdos272.Counting.GlobalSparse42

/-! Linear omitter payment from actual root resources, including exact
restoration of the entire retained-star branch of the original family. -/
namespace JSP233.LinearOmitters43
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32
open HarmonicAbel29 DenseDeletion40
open scoped Classical BigOperators
noncomputable section

theorem concentration_numeric (n C : ℝ) (hC : 1≤C) (hn : 65536*C≤n) :
    n^2/320 < 83*n^2/23040-(2*C+53/2)*n-2*C+1 := by
  have hn0 : 0≤n := by linarith
  have hn1 : 65536≤n := by linarith
  have ha := mul_nonneg (by linarith : 0≤n-65536*C) hn0
  have hb := mul_nonneg (by linarith : 0≤C-1) hn0
  have hc := mul_nonneg (by linarith : 0≤n-65536) (by linarith : 0≤C)
  have hd := mul_nonneg (by linarith : 0≤C) hn0
  nlinarith only [ha,hb,hc,hd]

theorem linear_numeric_payment (n C h k f pairs : ℝ)
    (hC : 1≤C) (hn : 65536*C≤n) (hh : h≤C*(n+1)) (hk : k≤1)
    (hbudget : f+n^2/50000≤h+k+pairs+n/4) : f<pairs+n+1 := by
  have hn0 : 0≤n := by linarith
  have hn1 : 65536≤n := by linarith
  have ha := mul_nonneg (by linarith : 0≤n-65536*C) hn0
  have hb := mul_nonneg (by linarith : 0≤n-65536) (by linarith : 0≤C)
  have hc := mul_nonneg (by linarith : 0≤C) hn0
  nlinarith only [ha,hb,hc,hbudget,hh,hk,hn1]

theorem actual_AP_lower (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ)) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ))
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card) :
    (((N-1:ℕ):ℝ)^2/18)-(2*C+7/2)*((N-1:ℕ):ℝ)-2*C+1≤
      (APLarge (RootPart F c)).card := by
  have hN : 65536≤N := by
    have hh : (65535:ℝ)≤((N-1:ℕ):ℝ) := by linarith
    have hh' : 65535≤N-1 := by exact_mod_cast hh
    omega
  obtain ⟨T,hT,hthird⟩ := OneThird32.actual_one_third_complement N c F hc hlegal htwo hkernel
  let V := (Ground N).erase c
  let q := (V\T).card
  have hV : V.card=N-1 := by dsimp [V]; rw [Finset.card_erase_of_mem hc,ground_card]
  have ht := transversal_complement_count V (Avoiders F c) T hT
  rw [hV] at ht
  have hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1) := by
    have ha := BudgetLoss31.actual_active_card_le N F c hlegal
    have hq := SingletonCapacity32.actual_ground_singleton_card_le hc hlegal
    have hdiv : (N-1)/4≤N-1 := Nat.div_le_self (N-1) 4
    omega
  have hj := actual_joint_budget_of_defect_supply c (Ground N) F hc hlegal (5*(N-1)) hsupply
  rw [ground_card] at hj
  have hM := StarBudget30.small_budget_identity N (by omega : 1≤N)
  have hnNat : N=(N-1)+1 := by omega
  have hreq : q.choose 2+2*(N-1)+2≤2*(Avoiders F c).card+
      2*(CommonKernel (Ground N) F c).card+(APLarge (RootPart F c)).card+5*(N-1) := by
    dsimp only [q,V] at *
    omega
  have hqNat : N-1≤3*q+3 := by dsimp [q,V]; omega
  have hqR : ((N-1:ℕ):ℝ)≤3*(q:ℝ)+3 := by exact_mod_cast hqNat
  have hnR : (65535:ℝ)≤((N-1:ℕ):ℝ) := by exact_mod_cast (show 65535≤N-1 by omega)
  have hfac : 0≤((q:ℝ)-(((N-1:ℕ):ℝ)-3)/3)*
      ((q:ℝ)+(((N-1:ℕ):ℝ)-3)/3-1) := by
    apply mul_nonneg <;> linarith
  have hchoose : ((((N-1:ℕ):ℝ)-3)*(((N-1:ℕ):ℝ)-6)/18)≤(q.choose 2:ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith only [hfac]
  have hreqR : (q.choose 2:ℝ)+2*((N-1:ℕ):ℝ)+2≤2*((Avoiders F c).card:ℝ)+
      2*((CommonKernel (Ground N) F c).card:ℝ)+(APLarge (RootPart F c)).card+5*((N-1:ℕ):ℝ) := by
    exact_mod_cast hreq
  have hkR : ((CommonKernel (Ground N) F c).card:ℝ)≤1 := by exact_mod_cast hkernel
  have hNR : (N:ℝ)=((N-1:ℕ):ℝ)+1 := by exact_mod_cast hnNat
  rw [hNR] at hcount
  nlinarith only [hchoose,hreqR,hcount,hkR]

theorem actual_low_active_lower (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ)) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ))
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card) :
    83*((N-1:ℕ):ℝ)^2/23040-(2*C+53/2)*((N-1:ℕ):ℝ)-2*C+1≤
      ∑ d∈LowActive c (APLarge (RootPart F c)),
        ((StepClass (APLarge (RootPart F c)) (trueStep c) (d:ℤ)).card:ℝ) := by
  let A := APLarge (RootPart F c)
  have hground : ∀ S∈A,S⊆Ground N := by
    intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S∈A,IsAP S := fun S hS=>(Finset.mem_filter.mp hS).2.1
  have hr : Rooted A c := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hsz : ∀ S∈A,4≤S.card := fun S hS=>(Finset.mem_filter.mp hS).2.2
  have ha := actual_AP_total N c A hground hAP hr hsz hc
  have hl := actual_AP_lower N c F C hC hn hc hlegal htwo hcount hkernel hcounter
  change (((N-1:ℕ):ℝ)^2/18)-(2*C+7/2)*((N-1:ℕ):ℝ)-2*C+1≤(A.card:ℝ) at hl
  have hH := LowSteps32.harmonic_linear (N-1)
  have hHH := mul_le_mul_of_nonneg_left hH (show (0:ℝ)≤2*((N-1:ℕ):ℝ) by positivity)
  change 83*((N-1:ℕ):ℝ)^2/23040-(2*C+53/2)*((N-1:ℕ):ℝ)-2*C+1≤
      ∑ d∈LowActive c A,((StepClass A (trueStep c) (d:ℤ)).card:ℝ)
  nlinarith only [ha,hl,hHH]

theorem actual_large_active_exists (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ)) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ))
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card) :
    ∃ d : ℤ,d∈APActiveSteps c (APLarge (RootPart F c)) ∧ d≤5 ∧
      (((N-1:ℕ):ℝ)^2/1600)≤((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ) := by
  let A := APLarge (RootPart F c)
  have hground : ∀ S∈A,S⊆Ground N := by
    intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S∈A,IsAP S := fun S hS=>(Finset.mem_filter.mp hS).2.1
  have hr : Rooted A c := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hsz : ∀ S∈A,4≤S.card := fun S hS=>(Finset.mem_filter.mp hS).2.2
  have hl := actual_low_active_lower N c F C hC hn hc hlegal htwo hcount hkernel hcounter
  have hstrict := concentration_numeric ((N-1:ℕ):ℝ) C hC hn
  have hl' : (((N-1:ℕ):ℝ)^2/320)<
      ∑ d∈LowActive c A,((StepClass A (trueStep c) (d:ℤ)).card:ℝ) := lt_of_lt_of_le hstrict hl
  obtain ⟨d,hd,ha,hd5,hcard⟩ := finite_low_pigeonhole ((N-1:ℕ):ℝ) (NatLabels c A)
    (fun d=>((StepClass A (trueStep c) (d:ℤ)).card:ℝ))
    (fun d=>(d:ℤ)∈APActiveSteps c A)
    (by intro d hd;exact (Finset.mem_Icc.mp (nat_labels_bound N c A hground hAP hr hsz hd)).1)
    (by convert hl' using 1;congr 1;ext d;simp only [LowActive,Finset.mem_filter])
  exact ⟨(d:ℤ),ha,by exact_mod_cast hd5,hcard⟩

theorem actual_linear_window_of_large_active_class
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ))
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (d : ℤ) (hactive : d∈APActiveSteps c (APLarge (RootPart F c)))
    (hlargeclass : (((N-1:ℕ):ℝ)^2/1600)≤
      ((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ)) :
    F.card<N.choose 2+1 := by
  let A := APLarge (RootPart F c)
  have hAP : ∀ S∈A,IsAP S := fun S hS=>(Finset.mem_filter.mp hS).2.1
  have hr : Rooted A c := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hsz : ∀ S∈A,4≤S.card := fun S hS=>(Finset.mem_filter.mp hS).2.2
  change d∈ActiveSteps c A (trueStep c) at hactive
  obtain ⟨hlabel,hleft,hright⟩ := Finset.mem_filter.mp hactive
  have hdpos := actual_step_labels_positive c A hAP hr d hlabel
  have hrep := actual_step_class_representation c A hAP hr hsz d
  have hn0 : (65535:ℝ)≤((N-1:ℕ):ℝ) := by linarith
  have hcard : 1000000<(StepClass A (trueStep c) d).card := by
    have hh : (1000000:ℝ)<((StepClass A (trueStep c) d).card:ℝ) := by
      dsimp only [A] at *
      nlinarith only [hlargeclass,hn0]
    exact_mod_cast hh
  have hs := AffineMiddleWitness31.actual_affine_pool_surplus_count c d hdpos
    (StepClass A (trueStep c) d) hrep hleft hright hcard
  have hsurplus : ((StepClass A (trueStep c) d).card:ℝ)+(((N-1:ℕ):ℝ)^2/50000)≤
      (AffineLine30.gcdStepPool c d (StepClass A (trueStep c) d)).card := by
    change (((N-1:ℕ):ℝ)^2/1600)≤((StepClass A (trueStep c) d).card:ℝ) at hlargeclass
    nlinarith only [hs,hlargeclass,sq_nonneg (((N-1:ℕ):ℝ))]
  have hb := BudgetLoss31.physical_budget_with_line_surplus N F c hc hlegal d hlabel _ hsurplus
  have hkR : ((CommonKernel (Ground N) F c).card:ℝ)≤1 := by exact_mod_cast hkernel
  have hN : 1≤N := by have := (mem_ground N c).mp hc;omega
  have hNR : (N:ℝ)=((N-1:ℕ):ℝ)+1 := by exact_mod_cast (show N=(N-1)+1 by omega)
  rw [hNR] at hcount
  have hf := linear_numeric_payment ((N-1:ℕ):ℝ) C (Avoiders F c).card
    (CommonKernel (Ground N) F c).card F.card ((N-1).choose 2) hC hn hcount hkR hb
  have hid := StarBudget30.small_budget_identity N hN
  rw [←hid]
  have hf' : (F.card:ℝ)<(N:ℝ)+((N-1).choose 2:ℕ) := by linarith
  exact_mod_cast hf'

theorem actual_small_kernel_linear_window
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ))
    (hkernel : (CommonKernel (Ground N) F c).card≤1) : F.card<N.choose 2+1 := by
  by_contra hno
  have hcounter : N.choose 2+1≤F.card := by omega
  obtain ⟨d,hd,hfive,hcard⟩ := actual_large_active_exists N c F C hC hn hc hlegal htwo hcount hkernel hcounter
  exact hno (actual_linear_window_of_large_active_class N F c C hC hn hc hlegal hcount hkernel d hd hcard)

theorem actual_crooked_linear_omitter_payment
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (C : ℝ)
    (hC : 1≤C) (hn : 65536*C≤((N-1:ℕ):ℝ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈Avoiders F c,¬IsAP S)
    (hcount : ((Avoiders F c).card:ℝ)≤C*(N:ℝ)) : F.card≤B N := by
  have hN : 65536≤N := by
    have hh : (65535:ℝ)≤((N-1:ℕ):ℝ) := by linarith
    have hh' : 65535≤N-1 := by exact_mod_cast hh
    omega
  by_cases hm : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hh := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc hlegal hm hk hbad
      omega
    · have hh := actual_small_kernel_linear_window N F c C hC hn hc hlegal hm hcount (by omega)
      unfold B
      omega
  · apply AnchorCompletion38.actual_crooked_omitter_middle_window N F c hN hc hlegal hbad
    omega

theorem actual_retained_star_avoiders {N r : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : Rooted (Retained N r F) c) :
    Avoiders F c⊆Deleted N r F ∧ ∀ S∈Avoiders F c,¬IsAP S := by
  have hsub : Avoiders F c⊆Deleted N r F := by
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    by_contra hnd
    exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnd⟩))
  exact ⟨hsub,fun S hS=>(Finset.mem_filter.mp (hsub hS)).2.1⟩

theorem actual_retained_star_original_payment {N r : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hr : 0<r) (hgate : (4*r^2+1)*(2*r-1)≤N)
    (hlinear : 65536*(4*r^2+1)≤N-1)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hroot : Rooted (Retained N r F) c) : F.card≤B N := by
  obtain ⟨hsub,hbad⟩ := actual_retained_star_avoiders hroot
  have hdel := DenseSharper41.actual_deleted_sharp hr hgate hlegal
  have hcount : (Avoiders F c).card≤(4*r^2+1)*N := (Finset.card_le_card hsub).trans hdel
  apply actual_crooked_linear_omitter_payment N F c ((4*r^2+1:ℕ):ℝ)
    (by exact_mod_cast (show 1≤4*r^2+1 by omega))
    (by exact_mod_cast hlinear) hc hlegal hbad
  exact_mod_cast hcount

theorem actual_retained_star_original_payment28 {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 2^49≤N) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hroot : Rooted (Retained N 28 F) c) : F.card≤B N := by
  apply actual_retained_star_original_payment (by decide : 0<28) ?_ ?_ hc hlegal hroot
  · norm_num
    omega
  · norm_num
    omega

theorem actual_original_nonstar_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,(∀ S∈Retained N 28 F,¬IsAP S → c∈S) ∧
      (¬∃ d∈Ground N,Rooted (Retained N 28 F) d) ∧
      Legal (Ground N) (Retained N 28 F) ∧ F.card≤(Retained N 28 F).card+3137*N ∧
      (∀ S∈F,IsAP S → S∈Retained N 28 F) := by
  obtain ⟨c,hc,hbad,hG,hsize,hAP⟩ := GlobalSparse42.actual_original_reduction28 hN hlegal hcounter
  refine ⟨c,hc,hbad,?_,hG,hsize,hAP⟩
  rintro ⟨d,hd,hroot⟩
  have hh := actual_retained_star_original_payment28 hN hd hlegal hroot
  omega

theorem actual_original_AP_avoider28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,(∀ S∈Retained N 28 F,¬IsAP S → c∈S) ∧
      ∃ S∈Retained N 28 F,IsAP S ∧ c∉S := by
  obtain ⟨c,hc,hbad,hnstar,hG,hsize,hAP⟩ := actual_original_nonstar_reduction28 hN hlegal hcounter
  have hnroot : ¬Rooted (Retained N 28 F) c := fun h=>hnstar ⟨c,hc,h⟩
  change ¬∀ S∈Retained N 28 F,c∈S at hnroot
  push Not at hnroot
  obtain ⟨S,hS,hcS⟩ := hnroot
  refine ⟨c,hc,hbad,S,hS,?_,hcS⟩
  by_contra hnot
  exact hcS (hbad S hS hnot)

#print axioms concentration_numeric
#print axioms linear_numeric_payment
#print axioms actual_AP_lower
#print axioms actual_low_active_lower
#print axioms actual_large_active_exists
#print axioms actual_linear_window_of_large_active_class
#print axioms actual_small_kernel_linear_window
#print axioms actual_crooked_linear_omitter_payment
#print axioms actual_retained_star_avoiders
#print axioms actual_retained_star_original_payment
#print axioms actual_retained_star_original_payment28
#print axioms actual_original_nonstar_reduction28
#print axioms actual_original_AP_avoider28
end
end JSP233.LinearOmitters43
