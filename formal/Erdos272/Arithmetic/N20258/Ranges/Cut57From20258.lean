module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source091
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_20493 :
    PopulationFees20258.bill (n:=20493) (PopulationFees20258.tabulate (20493-1) 256) source093.plan.table+
      4*20493*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*147014480465 := by decide +kernel
private theorem range57From20258To2571 : Segment 57 20258 20493 0 2571 :=
  paid (pc:=75) (v:=147014480465) (by decide) source093_valid tests57_093_0 fee57_093_20493 (by decide +kernel)

private theorem tests57_093_2571 : ∀ z∈source093.plan.table,z.1.Valid 57 2571 := by decide +kernel
private theorem range57From20258To2591 : Segment 57 20258 20493 2571 2591 :=
  paid (pc:=75) (v:=147014480465) (by decide) source093_valid tests57_093_2571 fee57_093_20493 (by decide +kernel)

private theorem tests57_093_2591 : ∀ z∈source093.plan.table,z.1.Valid 57 2591 := by decide +kernel
private theorem range57From20258To2593 : Segment 57 20258 20493 2591 2593 :=
  paid (pc:=75) (v:=147014480465) (by decide) source093_valid tests57_093_2591 fee57_093_20493 (by decide +kernel)

private theorem tests57_091_2593 : ∀ z∈source091.plan.table,z.1.Valid 57 2593 := by decide +kernel
private theorem fee57_091_20493 :
    PopulationFees20258.bill (n:=20493) (PopulationFees20258.tabulate (20493-1) 256) source091.plan.table+
      4*20493*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*241190521552 := by decide +kernel
private theorem range57From20258To2681 : Segment 57 20258 20493 2593 2681 :=
  paid (pc:=74) (v:=241190521552) (by decide) source091_valid tests57_091_2593 fee57_091_20493 (by decide +kernel)

private theorem tests57_094_2681 : ∀ z∈source094.plan.table,z.1.Valid 57 2681 := by decide +kernel
private theorem fee57_094_20493 :
    PopulationFees20258.bill (n:=20493) (PopulationFees20258.tabulate (20493-1) 256) source094.plan.table+
      4*20493*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*220927817282 := by decide +kernel
private theorem range57From20258To2878 : Segment 57 20258 20493 2681 2878 :=
  paid (pc:=73) (v:=220927817282) (by decide) source094_valid tests57_094_2681 fee57_094_20493 (by decide +kernel)

private theorem tests57_092_2878 : ∀ z∈source092.plan.table,z.1.Valid 57 2878 := by decide +kernel
private theorem fee57_092_20493 :
    PopulationFees20258.bill (n:=20493) (PopulationFees20258.tabulate (20493-1) 256) source092.plan.table+
      4*20493*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*207861474391 := by decide +kernel
private theorem range57From20258To3021 : Segment 57 20258 20493 2878 3021 :=
  paid (pc:=71) (v:=207861474391) (by decide) source092_valid tests57_092_2878 fee57_092_20493 (by decide +kernel)

private theorem tests57_097_3021 : ∀ z∈source097.plan.table,z.1.Valid 57 3021 := by decide +kernel
private theorem fee57_097_20493 :
    PopulationFees20258.bill (n:=20493) (PopulationFees20258.tabulate (20493-1) 256) source097.plan.table+
      4*20493*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*231481512026 := by decide +kernel
private theorem range57From20258To3193 : Segment 57 20258 20493 3021 3193 :=
  paid (pc:=69) (v:=231481512026) (by decide) source097_valid tests57_097_3021 fee57_097_20493 (by decide +kernel)

private theorem range57From20258 : Win 57 20258 20493 :=
  complete (by decide) (by decide) (join_population (join_population range57From20258To2571 (join_population range57From20258To2591 range57From20258To2593)) (join_population (join_population range57From20258To2681 range57From20258To2878) (join_population range57From20258To3021 range57From20258To3193)))

private theorem fee57_093_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source093.plan.table+
      4*20760*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*150527443147 := by decide +kernel
private theorem range57From20494To2574 : Segment 57 20494 20760 0 2574 :=
  paid (pc:=75) (v:=150527443147) (by decide) source093_valid tests57_093_0 fee57_093_20760 (by decide +kernel)

private theorem tests57_093_2574 : ∀ z∈source093.plan.table,z.1.Valid 57 2574 := by decide +kernel
private theorem range57From20494To2592 : Segment 57 20494 20760 2574 2592 :=
  paid (pc:=75) (v:=150527443147) (by decide) source093_valid tests57_093_2574 fee57_093_20760 (by decide +kernel)

private theorem tests57_093_2592 : ∀ z∈source093.plan.table,z.1.Valid 57 2592 := by decide +kernel
private theorem range57From20494To2593 : Segment 57 20494 20760 2592 2593 :=
  paid (pc:=75) (v:=150527443147) (by decide) source093_valid tests57_093_2592 fee57_093_20760 (by decide +kernel)

private theorem fee57_091_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source091.plan.table+
      4*20760*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*246962926905 := by decide +kernel
private theorem range57From20494To2670 : Segment 57 20494 20760 2593 2670 :=
  paid (pc:=75) (v:=246962926905) (by decide) source091_valid tests57_091_2593 fee57_091_20760 (by decide +kernel)

private theorem tests57_094_2670 : ∀ z∈source094.plan.table,z.1.Valid 57 2670 := by decide +kernel
private theorem fee57_094_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source094.plan.table+
      4*20760*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*226152256109 := by decide +kernel
private theorem range57From20494To2860 : Segment 57 20494 20760 2670 2860 :=
  paid (pc:=73) (v:=226152256109) (by decide) source094_valid tests57_094_2670 fee57_094_20760 (by decide +kernel)

private theorem tests57_092_2860 : ∀ z∈source092.plan.table,z.1.Valid 57 2860 := by decide +kernel
private theorem fee57_092_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source092.plan.table+
      4*20760*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*212865977079 := by decide +kernel
private theorem range57From20494To2995 : Segment 57 20494 20760 2860 2995 :=
  paid (pc:=72) (v:=212865977079) (by decide) source092_valid tests57_092_2860 fee57_092_20760 (by decide +kernel)

private theorem tests57_097_2995 : ∀ z∈source097.plan.table,z.1.Valid 57 2995 := by decide +kernel
private theorem fee57_097_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source097.plan.table+
      4*20760*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*236947106945 := by decide +kernel
private theorem range57From20494To3193 : Segment 57 20494 20760 2995 3193 :=
  paid (pc:=69) (v:=236947106945) (by decide) source097_valid tests57_097_2995 fee57_097_20760 (by decide +kernel)

private theorem range57From20494 : Win 57 20494 20760 :=
  complete (by decide) (by decide) (join_population (join_population range57From20494To2574 (join_population range57From20494To2592 range57From20494To2593)) (join_population (join_population range57From20494To2670 range57From20494To2860) (join_population range57From20494To2995 range57From20494To3193)))

private theorem fee57_093_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source093.plan.table+
      4*21065*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*154592285339 := by decide +kernel
private theorem range57From20761To2574 : Segment 57 20761 21065 0 2574 :=
  paid (pc:=76) (v:=154592285339) (by decide) source093_valid tests57_093_0 fee57_093_21065 (by decide +kernel)

private theorem range57From20761To2591 : Segment 57 20761 21065 2574 2591 :=
  paid (pc:=75) (v:=154592285339) (by decide) source093_valid tests57_093_2574 fee57_093_21065 (by decide +kernel)

private theorem range57From20761To2593 : Segment 57 20761 21065 2591 2593 :=
  paid (pc:=75) (v:=154592285339) (by decide) source093_valid tests57_093_2591 fee57_093_21065 (by decide +kernel)

private theorem fee57_091_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source091.plan.table+
      4*21065*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*253490506277 := by decide +kernel
private theorem range57From20761To2658 : Segment 57 20761 21065 2593 2658 :=
  paid (pc:=75) (v:=253490506277) (by decide) source091_valid tests57_091_2593 fee57_091_21065 (by decide +kernel)

private theorem tests57_095_2658 : ∀ z∈source095.plan.table,z.1.Valid 57 2658 := by decide +kernel
private theorem fee57_095_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source095.plan.table+
      4*21065*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*239113223224 := by decide +kernel
private theorem range57From20761To2780 : Segment 57 20761 21065 2658 2780 :=
  paid (pc:=74) (v:=239113223224) (by decide) source095_valid tests57_095_2658 fee57_095_21065 (by decide +kernel)

private theorem tests57_094_2780 : ∀ z∈source094.plan.table,z.1.Valid 57 2780 := by decide +kernel
private theorem fee57_094_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source094.plan.table+
      4*21065*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*232176481376 := by decide +kernel
private theorem range57From20761To2843 : Segment 57 20761 21065 2780 2843 :=
  paid (pc:=73) (v:=232176481376) (by decide) source094_valid tests57_094_2780 fee57_094_21065 (by decide +kernel)

private theorem tests57_092_2843 : ∀ z∈source092.plan.table,z.1.Valid 57 2843 := by decide +kernel
private theorem fee57_092_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source092.plan.table+
      4*21065*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*218519195753 := by decide +kernel
private theorem range57From20761To2967 : Segment 57 20761 21065 2843 2967 :=
  paid (pc:=72) (v:=218519195753) (by decide) source092_valid tests57_092_2843 fee57_092_21065 (by decide +kernel)

private theorem tests57_097_2967 : ∀ z∈source097.plan.table,z.1.Valid 57 2967 := by decide +kernel
private theorem fee57_097_21065 :
    PopulationFees20258.bill (n:=21065) (PopulationFees20258.tabulate (21065-1) 256) source097.plan.table+
      4*21065*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*243265051176 := by decide +kernel
private theorem range57From20761To3193 : Segment 57 20761 21065 2967 3193 :=
  paid (pc:=70) (v:=243265051176) (by decide) source097_valid tests57_097_2967 fee57_097_21065 (by decide +kernel)

private theorem range57From20761 : Win 57 20761 21065 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range57From20761To2574 range57From20761To2591) (join_population range57From20761To2593 range57From20761To2658)) (join_population (join_population range57From20761To2780 range57From20761To2843) (join_population range57From20761To2967 range57From20761To3193)))

theorem cut57From20258 : Win 57 20258 21065 :=
  (join_ground range57From20258 (join_ground range57From20494 range57From20761))

end JSP233.FiniteCutRanges20258
