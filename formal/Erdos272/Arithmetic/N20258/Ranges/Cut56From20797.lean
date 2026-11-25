module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source088
public import Erdos272.Arithmetic.N20258.Sources.Source089
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source091
public import Erdos272.Arithmetic.N20258.Sources.Source092

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests56_088_0 : ∀ z∈source088.plan.table,z.1.Valid 56 0 := by decide +kernel
private theorem fee56_088_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source088.plan.table+
      4*21120*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*166013661686 := by decide +kernel
private theorem range56From20797To2509 : Segment 56 20797 21120 0 2509 :=
  paid (pc:=76) (v:=166013661686) (by decide) source088_valid tests56_088_0 fee56_088_21120 (by decide +kernel)

private theorem tests56_088_2509 : ∀ z∈source088.plan.table,z.1.Valid 56 2509 := by decide +kernel
private theorem range56From20797To2525 : Segment 56 20797 21120 2509 2525 :=
  paid (pc:=76) (v:=166013661686) (by decide) source088_valid tests56_088_2509 fee56_088_21120 (by decide +kernel)

private theorem tests56_083_2525 : ∀ z∈source083.plan.table,z.1.Valid 56 2525 := by decide +kernel
private theorem fee56_083_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source083.plan.table+
      4*21120*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*214366157758 := by decide +kernel
private theorem range56From20797To2550 : Segment 56 20797 21120 2525 2550 :=
  paid (pc:=76) (v:=214366157758) (by decide) source083_valid tests56_083_2525 fee56_083_21120 (by decide +kernel)

private theorem tests56_083_2550 : ∀ z∈source083.plan.table,z.1.Valid 56 2550 := by decide +kernel
private theorem range56From20797To2552 : Segment 56 20797 21120 2550 2552 :=
  paid (pc:=76) (v:=214366157758) (by decide) source083_valid tests56_083_2550 fee56_083_21120 (by decide +kernel)

private theorem tests56_091_2552 : ∀ z∈source091.plan.table,z.1.Valid 56 2552 := by decide +kernel
private theorem fee56_091_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source091.plan.table+
      4*21120*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*254767165295 := by decide +kernel
private theorem range56From20797To2650 : Segment 56 20797 21120 2552 2650 :=
  paid (pc:=75) (v:=254767165295) (by decide) source091_valid tests56_091_2552 fee56_091_21120 (by decide +kernel)

private theorem tests56_089_2650 : ∀ z∈source089.plan.table,z.1.Valid 56 2650 := by decide +kernel
private theorem fee56_089_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source089.plan.table+
      4*21120*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*245596458658 := by decide +kernel
private theorem range56From20797To2729 : Segment 56 20797 21120 2650 2729 :=
  paid (pc:=74) (v:=245596458658) (by decide) source089_valid tests56_089_2650 fee56_089_21120 (by decide +kernel)

private theorem tests56_085_2729 : ∀ z∈source085.plan.table,z.1.Valid 56 2729 := by decide +kernel
private theorem fee56_085_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source085.plan.table+
      4*21120*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*235842011817 := by decide +kernel
private theorem range56From20797To2813 : Segment 56 20797 21120 2729 2813 :=
  paid (pc:=73) (v:=235842011817) (by decide) source085_valid tests56_085_2729 fee56_085_21120 (by decide +kernel)

private theorem tests56_092_2813 : ∀ z∈source092.plan.table,z.1.Valid 56 2813 := by decide +kernel
private theorem fee56_092_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source092.plan.table+
      4*21120*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*219654445906 := by decide +kernel
private theorem range56From20797To2960 : Segment 56 20797 21120 2813 2960 :=
  paid (pc:=72) (v:=219654445906) (by decide) source092_valid tests56_092_2813 fee56_092_21120 (by decide +kernel)

private theorem tests56_090_2960 : ∀ z∈source090.plan.table,z.1.Valid 56 2960 := by decide +kernel
private theorem fee56_090_21120 :
    PopulationFees20258.bill (n:=21120) (PopulationFees20258.tabulate (21120-1) 256) source090.plan.table+
      4*21120*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*201849687851 := by decide +kernel
private theorem range56From20797To3081 : Segment 56 20797 21120 2960 3081 :=
  paid (pc:=71) (v:=201849687851) (by decide) source090_valid tests56_090_2960 fee56_090_21120 (by decide +kernel)

private theorem range56From20797 : Win 56 20797 21120 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range56From20797To2509 range56From20797To2525) (join_population range56From20797To2550 range56From20797To2552)) (join_population (join_population range56From20797To2650 range56From20797To2729) (join_population range56From20797To2813 (join_population range56From20797To2960 range56From20797To3081))))

private theorem fee56_088_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source088.plan.table+
      4*21486*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*171172637152 := by decide +kernel
private theorem range56From21121To2514 : Segment 56 21121 21486 0 2514 :=
  paid (pc:=76) (v:=171172637152) (by decide) source088_valid tests56_088_0 fee56_088_21486 (by decide +kernel)

private theorem tests56_088_2514 : ∀ z∈source088.plan.table,z.1.Valid 56 2514 := by decide +kernel
private theorem range56From21121To2530 : Segment 56 21121 21486 2514 2530 :=
  paid (pc:=76) (v:=171172637152) (by decide) source088_valid tests56_088_2514 fee56_088_21486 (by decide +kernel)

private theorem tests56_083_2530 : ∀ z∈source083.plan.table,z.1.Valid 56 2530 := by decide +kernel
private theorem fee56_083_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source083.plan.table+
      4*21486*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*221102264956 := by decide +kernel
private theorem range56From21121To2550 : Segment 56 21121 21486 2530 2550 :=
  paid (pc:=76) (v:=221102264956) (by decide) source083_valid tests56_083_2530 fee56_083_21486 (by decide +kernel)

private theorem range56From21121To2552 : Segment 56 21121 21486 2550 2552 :=
  paid (pc:=76) (v:=221102264956) (by decide) source083_valid tests56_083_2550 fee56_083_21486 (by decide +kernel)

private theorem fee56_091_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source091.plan.table+
      4*21486*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*262629398322 := by decide +kernel
private theorem range56From21121To2642 : Segment 56 21121 21486 2552 2642 :=
  paid (pc:=75) (v:=262629398322) (by decide) source091_valid tests56_091_2552 fee56_091_21486 (by decide +kernel)

private theorem tests56_089_2642 : ∀ z∈source089.plan.table,z.1.Valid 56 2642 := by decide +kernel
private theorem fee56_089_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source089.plan.table+
      4*21486*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*253164126485 := by decide +kernel
private theorem range56From21121To2718 : Segment 56 21121 21486 2642 2718 :=
  paid (pc:=74) (v:=253164126485) (by decide) source089_valid tests56_089_2642 fee56_089_21486 (by decide +kernel)

private theorem tests56_089_2718 : ∀ z∈source089.plan.table,z.1.Valid 56 2718 := by decide +kernel
private theorem range56From21121To2720 : Segment 56 21121 21486 2718 2720 :=
  paid (pc:=74) (v:=253164126485) (by decide) source089_valid tests56_089_2718 fee56_089_21486 (by decide +kernel)

private theorem tests56_085_2720 : ∀ z∈source085.plan.table,z.1.Valid 56 2720 := by decide +kernel
private theorem fee56_085_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source085.plan.table+
      4*21486*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*243238697732 := by decide +kernel
private theorem range56From21121To2798 : Segment 56 21121 21486 2720 2798 :=
  paid (pc:=74) (v:=243238697732) (by decide) source085_valid tests56_085_2720 fee56_085_21486 (by decide +kernel)

private theorem tests56_092_2798 : ∀ z∈source092.plan.table,z.1.Valid 56 2798 := by decide +kernel
private theorem fee56_092_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source092.plan.table+
      4*21486*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*226446782811 := by decide +kernel
private theorem range56From21121To2936 : Segment 56 21121 21486 2798 2936 :=
  paid (pc:=73) (v:=226446782811) (by decide) source092_valid tests56_092_2798 fee56_092_21486 (by decide +kernel)

private theorem tests56_090_2936 : ∀ z∈source090.plan.table,z.1.Valid 56 2936 := by decide +kernel
private theorem fee56_090_21486 :
    PopulationFees20258.bill (n:=21486) (PopulationFees20258.tabulate (21486-1) 256) source090.plan.table+
      4*21486*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*208117774121 := by decide +kernel
private theorem range56From21121To3081 : Segment 56 21121 21486 2936 3081 :=
  paid (pc:=71) (v:=208117774121) (by decide) source090_valid tests56_090_2936 fee56_090_21486 (by decide +kernel)

private theorem range56From21121 : Win 56 21121 21486 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range56From21121To2514 range56From21121To2530) (join_population range56From21121To2550 (join_population range56From21121To2552 range56From21121To2642))) (join_population (join_population range56From21121To2718 range56From21121To2720) (join_population range56From21121To2798 (join_population range56From21121To2936 range56From21121To3081))))

theorem cut56From20797 : Win 56 20797 21486 :=
  (join_ground range56From20797 range56From21121)

end JSP233.FiniteCutRanges20258
