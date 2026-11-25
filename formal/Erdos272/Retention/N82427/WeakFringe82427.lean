module

public import Erdos272.Retention.N158375.FringePlans158375
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.WeakFringe82427
open StarCompletion APGeometry AlignedPlans212 RootModel291012 FringePlans158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

theorem preparation {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 2000 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((333/1000) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (11/100 : ℝ)*N) :
    (E.card : ℝ) ≤ ((41/6) : ℝ)*Width N L R+((-9/2) : ℝ) := by
  have hn : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (4-1), d < prepPlan d ∧
      GateConstant d (prepPlan d) < (N : ℝ)*GateCoefficient (1000/333) (100/11) d (prepPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [prepPlan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((4 : ℝ)-1)*((4 : ℝ)-2)/2 <
      (N : ℝ)*((4 : ℝ)/(1000/333)-1-((4 : ℝ)-1)/(100/11)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 4) (k := (1000/333)) (p := 4) (u := (100/11))
    prepPlan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, prepPlan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms preparation


end
end JSP233.WeakFringe82427
