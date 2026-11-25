module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source093.plan.table+
      4*24260*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*200523202850 := by decide +kernel
private theorem range57From23653To2670 : Segment 57 23653 24260 0 2670 :=
  paid (pc:=76) (v:=200523202850) (by decide) source093_valid tests57_093_0 fee57_093_24260 (by decide +kernel)

private theorem tests57_094_2670 : ∀ z∈source094.plan.table,z.1.Valid 57 2670 := by decide +kernel
private theorem fee57_094_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source094.plan.table+
      4*24260*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*300138892872 := by decide +kernel
private theorem range57From23653To2818 : Segment 57 23653 24260 2670 2818 :=
  paid (pc:=75) (v:=300138892872) (by decide) source094_valid tests57_094_2670 fee57_094_24260 (by decide +kernel)

private theorem tests57_094_2818 : ∀ z∈source094.plan.table,z.1.Valid 57 2818 := by decide +kernel
private theorem range57From23653To2823 : Segment 57 23653 24260 2818 2823 :=
  paid (pc:=75) (v:=300138892872) (by decide) source094_valid tests57_094_2818 fee57_094_24260 (by decide +kernel)

private theorem tests57_092_2823 : ∀ z∈source092.plan.table,z.1.Valid 57 2823 := by decide +kernel
private theorem fee57_092_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source092.plan.table+
      4*24260*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*282867191482 := by decide +kernel
private theorem range57From23653To2910 : Segment 57 23653 24260 2823 2910 :=
  paid (pc:=75) (v:=282867191482) (by decide) source092_valid tests57_092_2823 fee57_092_24260 (by decide +kernel)

private theorem tests57_087_2910 : ∀ z∈source087.plan.table,z.1.Valid 57 2910 := by decide +kernel
private theorem fee57_087_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source087.plan.table+
      4*24260*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*282062777789 := by decide +kernel
private theorem range57From23653To2915 : Segment 57 23653 24260 2910 2915 :=
  paid (pc:=75) (v:=282062777789) (by decide) source087_valid tests57_087_2910 fee57_087_24260 (by decide +kernel)

private theorem tests57_097_2915 : ∀ z∈source097.plan.table,z.1.Valid 57 2915 := by decide +kernel
private theorem fee57_097_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source097.plan.table+
      4*24260*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*314570226141 := by decide +kernel
private theorem range57From23653To3138 : Segment 57 23653 24260 2915 3138 :=
  paid (pc:=73) (v:=314570226141) (by decide) source097_valid tests57_097_2915 fee57_097_24260 (by decide +kernel)

private theorem tests57_096_3138 : ∀ z∈source096.plan.table,z.1.Valid 57 3138 := by decide +kernel
private theorem fee57_096_24260 :
    PopulationFees20258.bill (n:=24260) (PopulationFees20258.tabulate (24260-1) 256) source096.plan.table+
      4*24260*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*292435030610 := by decide +kernel
private theorem range57From23653To3193 : Segment 57 23653 24260 3138 3193 :=
  paid (pc:=72) (v:=292435030610) (by decide) source096_valid tests57_096_3138 fee57_096_24260 (by decide +kernel)

private theorem range57From23653 : Win 57 23653 24260 :=
  complete (by decide) (by decide) (join_population (join_population range57From23653To2670 (join_population range57From23653To2818 range57From23653To2823)) (join_population (join_population range57From23653To2910 range57From23653To2915) (join_population range57From23653To3138 range57From23653To3193)))

private theorem fee57_093_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source093.plan.table+
      4*24959*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*211213150791 := by decide +kernel
private theorem range57From24261To2688 : Segment 57 24261 24959 0 2688 :=
  paid (pc:=76) (v:=211213150791) (by decide) source093_valid tests57_093_0 fee57_093_24959 (by decide +kernel)

private theorem tests57_094_2688 : ∀ z∈source094.plan.table,z.1.Valid 57 2688 := by decide +kernel
private theorem fee57_094_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source094.plan.table+
      4*24959*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*315951873117 := by decide +kernel
private theorem range57From24261To2820 : Segment 57 24261 24959 2688 2820 :=
  paid (pc:=75) (v:=315951873117) (by decide) source094_valid tests57_094_2688 fee57_094_24959 (by decide +kernel)

private theorem tests57_094_2820 : ∀ z∈source094.plan.table,z.1.Valid 57 2820 := by decide +kernel
private theorem range57From24261To2825 : Segment 57 24261 24959 2820 2825 :=
  paid (pc:=75) (v:=315951873117) (by decide) source094_valid tests57_094_2820 fee57_094_24959 (by decide +kernel)

private theorem tests57_092_2825 : ∀ z∈source092.plan.table,z.1.Valid 57 2825 := by decide +kernel
private theorem fee57_092_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source092.plan.table+
      4*24959*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*298006414125 := by decide +kernel
private theorem range57From24261To2907 : Segment 57 24261 24959 2825 2907 :=
  paid (pc:=75) (v:=298006414125) (by decide) source092_valid tests57_092_2825 fee57_092_24959 (by decide +kernel)

private theorem tests57_087_2907 : ∀ z∈source087.plan.table,z.1.Valid 57 2907 := by decide +kernel
private theorem fee57_087_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source087.plan.table+
      4*24959*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*297084142889 := by decide +kernel
private theorem range57From24261To2913 : Segment 57 24261 24959 2907 2913 :=
  paid (pc:=75) (v:=297084142889) (by decide) source087_valid tests57_087_2907 fee57_087_24959 (by decide +kernel)

private theorem tests57_087_2913 : ∀ z∈source087.plan.table,z.1.Valid 57 2913 := by decide +kernel
private theorem range57From24261To2914 : Segment 57 24261 24959 2913 2914 :=
  paid (pc:=75) (v:=297084142889) (by decide) source087_valid tests57_087_2913 fee57_087_24959 (by decide +kernel)

private theorem tests57_097_2914 : ∀ z∈source097.plan.table,z.1.Valid 57 2914 := by decide +kernel
private theorem fee57_097_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source097.plan.table+
      4*24959*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*331160921136 := by decide +kernel
private theorem range57From24261To3114 : Segment 57 24261 24959 2914 3114 :=
  paid (pc:=73) (v:=331160921136) (by decide) source097_valid tests57_097_2914 fee57_097_24959 (by decide +kernel)

private theorem tests57_096_3114 : ∀ z∈source096.plan.table,z.1.Valid 57 3114 := by decide +kernel
private theorem fee57_096_24959 :
    PopulationFees20258.bill (n:=24959) (PopulationFees20258.tabulate (24959-1) 256) source096.plan.table+
      4*24959*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*307898920410 := by decide +kernel
private theorem range57From24261To3193 : Segment 57 24261 24959 3114 3193 :=
  paid (pc:=72) (v:=307898920410) (by decide) source096_valid tests57_096_3114 fee57_096_24959 (by decide +kernel)

private theorem range57From24261 : Win 57 24261 24959 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range57From24261To2688 range57From24261To2820) (join_population range57From24261To2825 range57From24261To2907)) (join_population (join_population range57From24261To2913 range57From24261To2914) (join_population range57From24261To3114 range57From24261To3193)))

private theorem fee57_093_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source093.plan.table+
      4*25762*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*224203675550 := by decide +kernel
private theorem range57From24960To2709 : Segment 57 24960 25762 0 2709 :=
  paid (pc:=76) (v:=224203675550) (by decide) source093_valid tests57_093_0 fee57_093_25762 (by decide +kernel)

private theorem tests57_094_2709 : ∀ z∈source094.plan.table,z.1.Valid 57 2709 := by decide +kernel
private theorem fee57_094_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source094.plan.table+
      4*25762*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*335108369691 := by decide +kernel
private theorem range57From24960To2826 : Segment 57 24960 25762 2709 2826 :=
  paid (pc:=76) (v:=335108369691) (by decide) source094_valid tests57_094_2709 fee57_094_25762 (by decide +kernel)

private theorem tests57_092_2826 : ∀ z∈source092.plan.table,z.1.Valid 57 2826 := by decide +kernel
private theorem fee57_092_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source092.plan.table+
      4*25762*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*315980721673 := by decide +kernel
private theorem range57From24960To2908 : Segment 57 24960 25762 2826 2908 :=
  paid (pc:=75) (v:=315980721673) (by decide) source092_valid tests57_092_2826 fee57_092_25762 (by decide +kernel)

private theorem tests57_087_2908 : ∀ z∈source087.plan.table,z.1.Valid 57 2908 := by decide +kernel
private theorem fee57_087_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source087.plan.table+
      4*25762*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*315255449128 := by decide +kernel
private theorem range57From24960To2913 : Segment 57 24960 25762 2908 2913 :=
  paid (pc:=75) (v:=315255449128) (by decide) source087_valid tests57_087_2908 fee57_087_25762 (by decide +kernel)

private theorem range57From24960To2914 : Segment 57 24960 25762 2913 2914 :=
  paid (pc:=75) (v:=315255449128) (by decide) source087_valid tests57_087_2913 fee57_087_25762 (by decide +kernel)

private theorem fee57_097_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source097.plan.table+
      4*25762*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*351277176232 := by decide +kernel
private theorem range57From24960To3093 : Segment 57 24960 25762 2914 3093 :=
  paid (pc:=74) (v:=351277176232) (by decide) source097_valid tests57_097_2914 fee57_097_25762 (by decide +kernel)

private theorem tests57_096_3093 : ∀ z∈source096.plan.table,z.1.Valid 57 3093 := by decide +kernel
private theorem fee57_096_25762 :
    PopulationFees20258.bill (n:=25762) (PopulationFees20258.tabulate (25762-1) 256) source096.plan.table+
      4*25762*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*326696331050 := by decide +kernel
private theorem range57From24960To3193 : Segment 57 24960 25762 3093 3193 :=
  paid (pc:=73) (v:=326696331050) (by decide) source096_valid tests57_096_3093 fee57_096_25762 (by decide +kernel)

private theorem range57From24960 : Win 57 24960 25762 :=
  complete (by decide) (by decide) (join_population (join_population range57From24960To2709 (join_population range57From24960To2826 range57From24960To2908)) (join_population (join_population range57From24960To2913 range57From24960To2914) (join_population range57From24960To3093 range57From24960To3193)))

theorem cut57From23653 : Win 57 23653 25762 :=
  (join_ground range57From23653 (join_ground range57From24261 range57From24960))

end JSP233.FiniteCutRanges20258
