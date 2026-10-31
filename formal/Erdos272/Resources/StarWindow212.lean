import Erdos272.Resources.DenseDeletion208
import Erdos272.Capacity.LowSteps32
import Erdos272.Core.OneThird32
import Erdos272.Capacity.SingletonCapacity32
import Erdos272.Arithmetic.HarmonicSharp39

/-! Retained-star recovery on the entire new finite formalization window.

The harmonic cutoff is deliberately coarse: `N < 2^26` gives `H_(N-1) < 19`.
All five low-step classes are paid together, using their actual disjoint
step pools and the existing `1/21` affine surplus theorem.
-/
namespace JSP233.StarWindow212
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32
open HarmonicAbel29 DenseDeletion40
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_AP_lower {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 65536≤N) (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card) :
    (((N-1:ℕ):ℝ)^2/18)-(7/2:ℝ)*((N-1:ℕ):ℝ)-
      2*(Avoiders F c).card+1≤(APLarge (RootPart F c)).card := by
  obtain ⟨T,hT,hthird⟩ := OneThird32.actual_one_third_complement N c F hc hF htwo hkernel
  let V := (Ground N).erase c
  let q := (V\T).card
  have hV : V.card=N-1 := by dsimp [V]; rw [Finset.card_erase_of_mem hc,ground_card]
  have ht := transversal_complement_count V (Avoiders F c) T hT
  rw [hV] at ht
  have hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1) := by
    have ha := BudgetLoss31.actual_active_card_le N F c hF
    have hq := SingletonCapacity32.actual_ground_singleton_card_le hc hF
    have hdiv : (N-1)/4≤N-1 := Nat.div_le_self (N-1) 4
    omega
  have hj := actual_joint_budget_of_defect_supply c (Ground N) F hc hF (5*(N-1)) hsupply
  rw [ground_card] at hj
  have hM := StarBudget30.small_budget_identity N (by omega : 1≤N)
  have hreq : q.choose 2+2*(N-1)+2≤2*(Avoiders F c).card+
      2*(CommonKernel (Ground N) F c).card+(APLarge (RootPart F c)).card+5*(N-1) := by
    dsimp only [q,V] at *
    omega
  have hqNat : N-1≤3*q+3 := by dsimp [q,V]; omega
  have hqR : ((N-1:ℕ):ℝ)≤3*(q:ℝ)+3 := by exact_mod_cast hqNat
  have hnR : (65535:ℝ)≤((N-1:ℕ):ℝ) := by
    exact_mod_cast (show 65535≤N-1 by omega)
  have hfac : 0≤((q:ℝ)-(((N-1:ℕ):ℝ)-3)/3)*
      ((q:ℝ)+(((N-1:ℕ):ℝ)-3)/3-1) := by
    apply mul_nonneg <;> linarith
  have hchoose : ((((N-1:ℕ):ℝ)-3)*(((N-1:ℕ):ℝ)-6)/18)≤(q.choose 2:ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith only [hfac]
  have hreqR : (q.choose 2:ℝ)+2*((N-1:ℕ):ℝ)+2≤2*((Avoiders F c).card:ℝ)+
      2*((CommonKernel (Ground N) F c).card:ℝ)+(APLarge (RootPart F c)).card+
        5*((N-1:ℕ):ℝ) := by exact_mod_cast hreq
  have hkR : ((CommonKernel (Ground N) F c).card:ℝ)≤1 := by exact_mod_cast hkernel
  nlinarith only [hchoose,hreqR,hkR]

theorem actual_budget_with_many_surpluses {N : ℕ} {c : ℤ}
    {F : Finset (Finset ℤ)} (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (D : Finset ℤ)
    (hD : D⊆APActiveSteps c (APLarge (RootPart F c)))
    (hbig : ∀d∈D,1000000<(StepClass (APLarge (RootPart F c)) (trueStep c) d).card) :
    (F.card:ℝ)+(∑d∈D,((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ))/21≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
        ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 := by
  let A := APLarge (RootPart F c)
  have hAP : ∀S∈A,IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀S∈A,4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have hlabels : D⊆StepLabels A (trueStep c) := by
    intro d hd
    exact (Finset.mem_filter.mp (hD hd)).1
  let loss : ℤ→ℝ := fun d => if d∈D then (StepClass A (trueStep c) d).card/21 else 0
  have hpoint : ∀d∈StepLabels A (trueStep c),
      ((StepClass A (trueStep c) d).card:ℝ)+loss d≤
        (AffineLine30.gcdStepPool c d (StepClass A (trueStep c) d)).card+
          (if d∈APActiveSteps c A then (1:ℝ) else 0) := by
    intro d hd
    by_cases hdD : d∈D
    · obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp (hD hdD)
      have hactive : d∈APActiveSteps c A := hD hdD
      have hp := actual_step_labels_positive c A hAP hroot d hd
      have hrep := actual_step_class_representation c A hAP hroot hlarge d
      have hs := AffineMiddleWitness31.actual_affine_pool_surplus_count c d hp
        (StepClass A (trueStep c) d) hrep hl hr (hbig d hdD)
      simp only [loss,if_pos hdD,if_pos hactive]
      linarith only [hs]
    · have hs := actual_step_class_count c A hAP hroot hlarge d hd
      have hsR : ((StepClass A (trueStep c) d).card:ℝ)≤
          (AffineLine30.gcdStepPool c d (StepClass A (trueStep c) d)).card+
            (if d∈APActiveSteps c A then (1:ℝ) else 0) := by exact_mod_cast hs
      simpa only [loss,if_neg hdD,add_zero] using hsR
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  have hsumA : (∑d∈StepLabels A (trueStep c),((StepClass A (trueStep c) d).card:ℝ))=A.card := by
    exact_mod_cast sum_stepClass_card A (trueStep c)
  have hsumP : (∑d∈StepLabels A (trueStep c),
      ((AffineLine30.gcdStepPool c d (StepClass A (trueStep c) d)).card:ℝ))=
        (APResourcePool c A).card := by
    exact_mod_cast sum_stepPool_card c A (trueStep c)
      (actual_step_labels_positive c A hAP hroot)
  have hsumI : (∑d∈StepLabels A (trueStep c),
      if d∈APActiveSteps c A then (1:ℝ) else 0)=(APActiveSteps c A).card := by
    exact_mod_cast sum_active_indicator c A (trueStep c)
  have hfilter : (StepLabels A (trueStep c)).filter (fun d=>d∈D)=D := by
    ext d
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hd => hlabels hd)
  have hsumL : (∑d∈StepLabels A (trueStep c),loss d)=
      (∑d∈D,((StepClass A (trueStep c) d).card:ℝ))/21 := by
    simp only [loss,←Finset.sum_filter,hfilter,Finset.sum_div]
  rw [hsumA,hsumP,hsumI,hsumL] at hs
  have hb := BudgetLoss31.actual_one_private_budget c (Ground N) F hc hF
  rw [ground_card] at hb
  have hbR : (F.card:ℝ)+(APResourcePool c A).card≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
        ((N-1).choose 2:ℕ)+(A.card:ℝ) := by exact_mod_cast hb
  have ha := BudgetLoss31.actual_active_card_le N F c hF
  change (APActiveSteps c A).card≤(N-1)/4 at ha
  have haR : ((APActiveSteps c A).card:ℝ)≤((N-1:ℕ):ℝ)/4 := by
    have h4 : 4*(APActiveSteps c A).card≤N-1 := by omega
    have h4R : (4:ℝ)*(APActiveSteps c A).card≤((N-1:ℕ):ℝ) := by exact_mod_cast h4
    linarith only [h4R]
  dsimp only [A] at hs hbR haR
  linarith only [hs,hbR,haR]

theorem actual_budget_with_low_surpluses {N : ℕ} {c : ℤ}
    {F : Finset (Finset ℤ)} (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    (F.card:ℝ)+((∑d∈LowActive c (APLarge (RootPart F c)),
      ((StepClass (APLarge (RootPart F c)) (trueStep c) (d:ℤ)).card:ℝ))-5000000)/21≤
        (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
          ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 := by
  let A := APLarge (RootPart F c)
  let L := LowActive c A
  let P : Finset ℕ := L.filter (fun d:ℕ=>1000000<(StepClass A (trueStep c) (d:ℤ)).card)
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
  have hbig : ∀d∈D,1000000<(StepClass A (trueStep c) d).card := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp he).2
  have hb := actual_budget_with_many_surpluses hc hF D hD hbig
  have hsumD : (∑d∈D,((StepClass A (trueStep c) d).card:ℝ))=
      ∑d∈P,((StepClass A (trueStep c) (d:ℤ)).card:ℝ) := by
    dsimp only [D]
    rw [Finset.sum_image]
    intro i _ j _ hij
    change (i:ℤ)=(j:ℤ) at hij
    exact_mod_cast hij
  have hsub : L⊆Finset.Icc 1 5 := by
    intro d hd
    have hdata := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (nat_labels_bound N c A hground hAP hroot hlarge hdata.1)).1,
       hdata.2.2⟩
  have hcard : L.card≤5 := by simpa using Finset.card_le_card hsub
  have hpoint : ∀d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ)≤
      (if 1000000<(StepClass A (trueStep c) (d:ℤ)).card then
        ((StepClass A (trueStep c) (d:ℤ)).card:ℝ) else 0)+1000000 := by
    intro d _
    split_ifs with hd
    · linarith
    · have hh : ((StepClass A (trueStep c) (d:ℤ)).card:ℝ)≤1000000 := by
        exact_mod_cast (show (StepClass A (trueStep c) (d:ℤ)).card≤1000000 by omega)
      linarith only [hh]
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul] at hs
  have hcR : (L.card:ℝ)≤5 := by exact_mod_cast hcard
  change (∑d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))≤
    (∑d∈P,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))+(L.card:ℝ)*1000000 at hs
  change (F.card:ℝ)+(∑d∈D,((StepClass A (trueStep c) d).card:ℝ))/21≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
        ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 at hb
  rw [hsumD] at hb
  change (F.card:ℝ)+((∑d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))-5000000)/21≤_
  linarith only [hs,hcR,hb]

theorem actual_small_kernel_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 656184≤N) (hhi : N≤62443451)
    (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcount : (Avoiders F c).card≤121*N+968) : F.card≤B N := by
  by_contra hn
  have hcounter : N.choose 2+1≤F.card := by unfold B at hn;omega
  have hlow := actual_AP_lower (by omega : 65536≤N) hc hF htwo hkernel hcounter
  let A := APLarge (RootPart F c)
  have hground : ∀S∈A,S⊆Ground N := fun S hS =>
    hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀S∈A,IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀S∈A,4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have htotal := actual_AP_total N c A hground hAP hroot hlarge hc
  have hpow : N-1<2^26 := by norm_num;omega
  have hH := HarmonicSharp39.actual_harmonic_tight (N-1) 26 hpow
  have hHpay := mul_le_mul_of_nonneg_left hH
    (show (0:ℝ)≤2*((N-1:ℕ):ℝ) by positivity)
  have hb := actual_budget_with_low_surpluses hc hF
  have hcountR : ((Avoiders F c).card:ℝ)≤121*((N-1:ℕ):ℝ)+1089 := by
    have hh : ((Avoiders F c).card:ℝ)≤121*(N:ℝ)+968 := by exact_mod_cast hcount
    have he : (N:ℝ)=((N-1:ℕ):ℝ)+1 := by exact_mod_cast (show N=(N-1)+1 by omega)
    linarith only [hh,he]
  have hkR : ((CommonKernel (Ground N) F c).card:ℝ)≤1 := by exact_mod_cast hkernel
  have hcounterR : ((N-1).choose 2:ℝ)+((N-1:ℕ):ℝ)+1≤F.card := by
    have hid := StarBudget30.small_budget_identity N (by omega : 1≤N)
    have hh : (N.choose 2:ℝ)+1≤F.card := by exact_mod_cast hcounter
    have hidR : (N.choose 2:ℝ)+1=(N:ℝ)+((N-1).choose 2:ℝ) := by exact_mod_cast hid.symm
    have he : (N:ℝ)=((N-1:ℕ):ℝ)+1 := by exact_mod_cast (show N=(N-1)+1 by omega)
    linarith only [hh,hidR,he]
  have hnR : (656183:ℝ)≤((N-1:ℕ):ℝ) := by
    exact_mod_cast (show 656183≤N-1 by omega)
  have hp := mul_nonneg (show (0:ℝ)≤((N-1:ℕ):ℝ)-656183 by linarith only [hnR])
    (show (0:ℝ)≤((N-1:ℕ):ℝ)+656183-505755 by linarith only [hnR])
  change (((N-1:ℕ):ℝ)^2/18)-(7/2:ℝ)*((N-1:ℕ):ℝ)-
      2*(Avoiders F c).card+1≤A.card at hlow
  change (F.card:ℝ)+((∑d∈LowActive c A,
      ((StepClass A (trueStep c) (d:ℤ)).card:ℝ))-5000000)/21≤_ at hb
  norm_num at hHpay
  nlinarith only [hlow,htotal,hHpay,hb,hcountR,hkR,hcounterR,hp,hnR]

theorem actual_retained_star_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 656184≤N) (hhi : N≤62443451)
    (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : Rooted (Retained N 11 F) c) : F.card≤B N := by
  have hsub : Avoiders F c⊆Deleted N 11 F := by
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    by_contra hnd
    exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnd⟩))
  have hbad : ∀S∈Avoiders F c,¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp (hsub hS)).2.1
  have hdel := DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) hF
  have hcount : (Avoiders F c).card≤121*N+968 := (Finset.card_le_card hsub).trans hdel
  by_cases htwo : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hb := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc hF htwo hk hbad
      omega
    · exact actual_small_kernel_window hN hhi hc hF htwo (by omega) hcount
  · apply AnchorCompletion38.actual_crooked_omitter_middle_window N F c (by omega) hc hF hbad
    omega

#print axioms actual_AP_lower
#print axioms actual_budget_with_many_surpluses
#print axioms actual_budget_with_low_surpluses
#print axioms actual_small_kernel_window
#print axioms actual_retained_star_window
end
end JSP233.StarWindow212
