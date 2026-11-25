module

public import Erdos272.Retention.N291012.FringeGeneric291012
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.FringePlans158375
open StarCompletion APGeometry AlignedPlans212 RootModel291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 158375

def prepPlan (d : ℕ) : ℕ := match d with
  | 1 => 4
  | 2 => 4
  | _ => 4

theorem preparation {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 158375 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/3) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/(10) : ℝ)*N) :
    (E.card : ℝ) ≤ ((13/2) : ℝ)*Width N L R+((-11/2) : ℝ) := by
  have hn : (158375 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (3-1), d < prepPlan d ∧
      GateConstant d (prepPlan d) < (N : ℝ)*GateCoefficient 3 (10) d (prepPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [prepPlan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((4 : ℝ)-1)*((4 : ℝ)-2)/2 <
      (N : ℝ)*((4 : ℝ)/3-1-((4 : ℝ)-1)/(10)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 3) (k := 3) (p := 4) (u := (10))
    prepPlan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, prepPlan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms preparation


def rank2lowPlan (d : ℕ) : ℕ := match d with
  | 1 => 3
  | _ => 3

theorem rank2low {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 158375 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/2) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/(1000/67) : ℝ)*N) :
    (E.card : ℝ) ≤ (4 : ℝ)*Width N L R+(-4 : ℝ) := by
  have hn : (158375 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (2-1), d < rank2lowPlan d ∧
      GateConstant d (rank2lowPlan d) < (N : ℝ)*GateCoefficient 2 (1000/67) d (rank2lowPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    have hdEq : d = 1 := by omega
    subst d
    norm_num [rank2lowPlan, GateConstant, GateCoefficient]
    linarith only [hn]
  have hoff : ((3 : ℝ)-1)*((3 : ℝ)-2)/2 <
      (N : ℝ)*((3 : ℝ)/2-1-((3 : ℝ)-1)/(1000/67)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 2) (k := 2) (p := 3) (u := (1000/67))
    rank2lowPlan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank2lowPlan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank2low

def rank2highPlan (d : ℕ) : ℕ := match d with
  | 1 => 2
  | _ => 2

theorem rank2high {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 158375 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((3/4) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/(1000/67) : ℝ)*N) :
    (E.card : ℝ) ≤ (2 : ℝ)*Width N L R+(-2 : ℝ) := by
  have hn : (158375 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (2-1), d < rank2highPlan d ∧
      GateConstant d (rank2highPlan d) < (N : ℝ)*GateCoefficient (4/3) (1000/67) d (rank2highPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    have hdEq : d = 1 := by omega
    subst d
    norm_num [rank2highPlan, GateConstant, GateCoefficient]
    linarith only [hn]
  have hoff : ((2 : ℝ)-1)*((2 : ℝ)-2)/2 <
      (N : ℝ)*((2 : ℝ)/(4/3)-1-((2 : ℝ)-1)/(1000/67)) := by
    norm_num
    omega
  have hh := FringeGeneric291012.actual_fringe_count (K := 2) (k := (4/3)) (p := 2) (u := (1000/67))
    rank2highPlan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank2highPlan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank2high

def rank3Plan (d : ℕ) : ℕ := match d with
  | 1 => 4
  | 2 => 4
  | _ => 4

theorem rank3 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 158375 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/3) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/(1000/67) : ℝ)*N) :
    (E.card : ℝ) ≤ ((13/2) : ℝ)*Width N L R+((-11/2) : ℝ) := by
  have hn : (158375 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (3-1), d < rank3Plan d ∧
      GateConstant d (rank3Plan d) < (N : ℝ)*GateCoefficient 3 (1000/67) d (rank3Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [rank3Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((4 : ℝ)-1)*((4 : ℝ)-2)/2 <
      (N : ℝ)*((4 : ℝ)/3-1-((4 : ℝ)-1)/(1000/67)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 3) (k := 3) (p := 4) (u := (1000/67))
    rank3Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank3Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank3


end
end JSP233.FringePlans158375
