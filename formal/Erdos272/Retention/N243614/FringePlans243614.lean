module

public import Erdos272.Retention.N291012.FringeGeneric291012
public import Erdos272.Resources.N291012.RootModel291012
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.FringePlans243614
open StarCompletion APGeometry AlignedPlans212 RootModel291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def prep1Plan (d : ℕ) : ℕ := match d with
  | 1 => 10
  | 2 => 7
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | _ => 10

theorem prep1 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((19/100) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/(21/2) : ℝ)*N) :
    (E.card : ℝ) ≤ ((1217/60) : ℝ)*Width N L R+((-257/20) : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (6-1), d < prep1Plan d ∧
      GateConstant d (prep1Plan d) < (N : ℝ)*GateCoefficient (100/19) (21/2) d (prep1Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [prep1Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((10 : ℝ)-1)*((10 : ℝ)-2)/2 <
      (N : ℝ)*((10 : ℝ)/(100/19)-1-((10 : ℝ)-1)/(21/2)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 6) (k := (100/19)) (p := 10) (u := (21/2))
    prep1Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, prep1Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms prep1

def rank2lowPlan (d : ℕ) : ℕ := match d with
  | 1 => 3
  | _ => 3

theorem rank2low {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/2) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ (4 : ℝ)*Width N L R+(-4 : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (2-1), d < rank2lowPlan d ∧
      GateConstant d (rank2lowPlan d) < (N : ℝ)*GateCoefficient 2 17 d (rank2lowPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    have hdEq : d = 1 := by omega
    subst d
    norm_num [rank2lowPlan, GateConstant, GateCoefficient]
    linarith only [hn]
  have hoff : ((3 : ℝ)-1)*((3 : ℝ)-2)/2 <
      (N : ℝ)*((3 : ℝ)/2-1-((3 : ℝ)-1)/17) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 2) (k := 2) (p := 3) (u := 17)
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
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((3/4) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ (2 : ℝ)*Width N L R+(-2 : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (2-1), d < rank2highPlan d ∧
      GateConstant d (rank2highPlan d) < (N : ℝ)*GateCoefficient (4/3) 17 d (rank2highPlan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    have hdEq : d = 1 := by omega
    subst d
    norm_num [rank2highPlan, GateConstant, GateCoefficient]
    linarith only [hn]
  have hoff : ((2 : ℝ)-1)*((2 : ℝ)-2)/2 <
      (N : ℝ)*((2 : ℝ)/(4/3)-1-((2 : ℝ)-1)/17) := by
    norm_num
    omega
  have hh := FringeGeneric291012.actual_fringe_count (K := 2) (k := (4/3)) (p := 2) (u := 17)
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
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/3) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ ((13/2) : ℝ)*Width N L R+((-11/2) : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (3-1), d < rank3Plan d ∧
      GateConstant d (rank3Plan d) < (N : ℝ)*GateCoefficient 3 17 d (rank3Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [rank3Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((4 : ℝ)-1)*((4 : ℝ)-2)/2 <
      (N : ℝ)*((4 : ℝ)/3-1-((4 : ℝ)-1)/17) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 3) (k := 3) (p := 4) (u := 17)
    rank3Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank3Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank3

def rank4Plan (d : ℕ) : ℕ := match d with
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | _ => 5

theorem rank4 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/4) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ ((28/3) : ℝ)*Width N L R+(-6 : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (4-1), d < rank4Plan d ∧
      GateConstant d (rank4Plan d) < (N : ℝ)*GateCoefficient 4 17 d (rank4Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [rank4Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((5 : ℝ)-1)*((5 : ℝ)-2)/2 <
      (N : ℝ)*((5 : ℝ)/4-1-((5 : ℝ)-1)/17) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 4) (k := 4) (p := 5) (u := 17)
    rank4Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank4Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank4

def rank5Plan (d : ℕ) : ℕ := match d with
  | 1 => 7
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | _ => 7

theorem rank5 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((1/5) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ ((163/12) : ℝ)*Width N L R+((-35/4) : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (5-1), d < rank5Plan d ∧
      GateConstant d (rank5Plan d) < (N : ℝ)*GateCoefficient 5 17 d (rank5Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [rank5Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((7 : ℝ)-1)*((7 : ℝ)-2)/2 <
      (N : ℝ)*((7 : ℝ)/5-1-((7 : ℝ)-1)/17) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 5) (k := 5) (p := 7) (u := 17)
    rank5Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank5Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank5

def rank6Plan (d : ℕ) : ℕ := match d with
  | 1 => 8
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | _ => 8

theorem rank6 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, ((19/100) : ℝ)*(N : ℝ) < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hwidth : Width N L R < (1/17 : ℝ)*N) :
    (E.card : ℝ) ≤ ((947/60) : ℝ)*Width N L R+((-187/20) : ℝ) := by
  have hn : (243614 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (6-1), d < rank6Plan d ∧
      GateConstant d (rank6Plan d) < (N : ℝ)*GateCoefficient (100/19) 17 d (rank6Plan d) := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [rank6Plan, GateConstant, GateCoefficient] <;> linarith only [hn]
  have hoff : ((8 : ℝ)-1)*((8 : ℝ)-2)/2 <
      (N : ℝ)*((8 : ℝ)/(100/19)-1-((8 : ℝ)-1)/17) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count (K := 6) (k := (100/19)) (p := 8) (u := 17)
    rank6Plan (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hwidth; nlinarith only [hwidth]) hplan hoff
  norm_num [Slope, Constant, rank6Plan, Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

#print axioms rank6

end
end JSP233.FringePlans243614
