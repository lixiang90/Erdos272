module

public import Erdos272.Resources.StarWindow212

@[expose] public section

namespace JSP233.StarLower65172
open StarCompletion StarResources30 CrossLine30 JointResources31 LowSteps32
open HarmonicAbel29 DenseDeletion40
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_AP_lower {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 7≤N) (hc : c∈Ground N) (hF : Legal (Ground N) F)
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
  have hnR : (6:ℝ)≤((N-1:ℕ):ℝ) := by
    exact_mod_cast (show 6≤N-1 by omega)
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

#print axioms actual_AP_lower
end
end JSP233.StarLower65172
