import Erdos272.Capacity.LowSteps32
import Erdos272.Core.OneThird32
import Erdos272.Capacity.SingletonCapacity32

/-! Actual complement, singleton classification and low-step concentration
assembled into the unconditional small-kernel middle-window bound. -/
namespace JSP233.MiddleWindow32
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32
open HarmonicAbel29
open scoped Classical BigOperators
noncomputable section

theorem actual_AP_lower (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hN : 65536≤N) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card)
    (hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1)) :
    (((N-1:ℕ):ℝ)^2/18)-15*((N-1:ℕ):ℝ)/2+9≤(APLarge (RootPart F c)).card := by
  obtain ⟨T,hT,hthird⟩ := OneThird32.actual_one_third_complement N c F hc hlegal htwo hkernel
  let V := (Ground N).erase c
  let q := (V\T).card
  have hV : V.card=N-1 := by dsimp [V]; rw [Finset.card_erase_of_mem hc,ground_card]
  have ht := transversal_complement_count V (Avoiders F c) T hT
  rw [hV] at ht
  dsimp only [V] at ht
  have hj := actual_joint_budget_of_defect_supply c (Ground N) F hc hlegal (5*(N-1)) hsupply
  rw [ground_card] at hj
  have hM := StarBudget30.small_budget_identity N (by omega : 1≤N)
  have hnNat : N=(N-1)+1 := by omega
  have hhcount : (Avoiders F c).card+4≤2*(N-1) := by omega
  have hreq : q.choose 2+8≤7*(N-1)+(APLarge (RootPart F c)).card := by
    dsimp only [q,V]
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
  have hreqR : (q.choose 2:ℝ)+8≤7*((N-1:ℕ):ℝ)+(APLarge (RootPart F c)).card := by
    exact_mod_cast hreq
  nlinarith only [hchoose,hreqR]

theorem actual_low_active_lower (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hN : 65536≤N) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card)
    (hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1)) :
    83*((N-1:ℕ):ℝ)^2/23040-61*((N-1:ℕ):ℝ)/2+9≤
      ∑ d∈LowActive c (APLarge (RootPart F c)),
        ((StepClass (APLarge (RootPart F c)) (trueStep c) (d:ℤ)).card:ℝ) := by
  let A := APLarge (RootPart F c)
  have hground : ∀ S∈A, S⊆Ground N := by
    intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S∈A, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀ S∈A, 4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have ha := actual_AP_total N c A hground hAP hroot hlarge hc
  have hl := actual_AP_lower N c F hN hc hlegal htwo hcount hkernel hcounter hsupply
  change (((N-1:ℕ):ℝ)^2/18)-15*((N-1:ℕ):ℝ)/2+9≤(A.card:ℝ) at hl
  have hH := LowSteps32.harmonic_linear (N-1)
  have hHH := mul_le_mul_of_nonneg_left hH (show (0:ℝ)≤2*((N-1:ℕ):ℝ) by positivity)
  change 83*((N-1:ℕ):ℝ)^2/23040-61*((N-1:ℕ):ℝ)/2+9≤
    ∑ d∈LowActive c A, ((StepClass A (trueStep c) (d:ℤ)).card:ℝ)
  nlinarith only [ha,hl,hHH]

theorem actual_large_active_exists (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hN : 65536≤N) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hcounter : N.choose 2+1≤F.card)
    (hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1)) :
    ∃ d : ℤ, d∈APActiveSteps c (APLarge (RootPart F c)) ∧ d≤5 ∧
      (((N-1:ℕ):ℝ)^2/1600)≤((StepClass (APLarge (RootPart F c)) (trueStep c) d).card:ℝ) := by
  let A := APLarge (RootPart F c)
  have hground : ∀ S∈A, S⊆Ground N := by
    intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S∈A, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀ S∈A, 4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have hl := actual_low_active_lower N c F hN hc hlegal htwo hcount hkernel hcounter hsupply
  have hnR : (65535:ℝ)≤((N-1:ℕ):ℝ) := by exact_mod_cast (show 65535≤N-1 by omega)
  have hstrict := concentration_numeric ((N-1:ℕ):ℝ) hnR
  have hl' : (((N-1:ℕ):ℝ)^2/320)<
      ∑ d∈LowActive c A, ((StepClass A (trueStep c) (d:ℤ)).card:ℝ) := lt_of_lt_of_le hstrict hl
  obtain ⟨d,hd,ha,hd5,hcard⟩ := finite_low_pigeonhole ((N-1:ℕ):ℝ) (NatLabels c A)
    (fun d => ((StepClass A (trueStep c) (d:ℤ)).card:ℝ))
    (fun d => (d:ℤ)∈APActiveSteps c A)
    (by intro d hd; exact (Finset.mem_Icc.mp (nat_labels_bound N c A hground hAP hroot hlarge hd)).1)
    (by convert hl' using 1; congr 1; ext d; simp only [LowActive,Finset.mem_filter])
  exact ⟨(d:ℤ),ha,by exact_mod_cast hd5,hcard⟩

theorem actual_middle_window_of_defect_capacity
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (hN : 65536≤N)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1)
    (hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤5*(N-1)) :
    F.card<N.choose 2+1 := by
  by_contra hn
  have hcounter : N.choose 2+1≤F.card := by omega
  obtain ⟨d,hd,hfive,hcard⟩ := actual_large_active_exists N c F hN hc hlegal htwo hcount hkernel hcounter hsupply
  exact hn (AffineMiddleWitness31.actual_middle_window_of_large_active_class N F c hN hc hlegal hcount hkernel d hd hcard)

theorem actual_small_kernel_middle_window
    (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) (hN : 65536≤N)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hcount : (Avoiders F c).card≤2*N-6)
    (hkernel : (CommonKernel (Ground N) F c).card≤1) :
    F.card<N.choose 2+1 := by
  apply actual_middle_window_of_defect_capacity N F c hN hc hlegal htwo hcount hkernel
  have ha := BudgetLoss31.actual_active_card_le N F c hlegal
  have hq := SingletonCapacity32.actual_ground_singleton_card_le hc hlegal
  have hdiv : (N-1)/4≤N-1 := Nat.div_le_self (N-1) 4
  omega

#print axioms actual_AP_lower
#print axioms actual_low_active_lower
#print axioms actual_large_active_exists
#print axioms actual_middle_window_of_defect_capacity
#print axioms actual_small_kernel_middle_window
end
end JSP233.MiddleWindow32
