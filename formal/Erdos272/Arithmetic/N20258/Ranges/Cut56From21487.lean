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
private theorem fee56_088_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source088.plan.table+
      4*21880*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*177047925916 := by decide +kernel
private theorem range56From21487To2529 : Segment 56 21487 21880 0 2529 :=
  paid (pc:=76) (v:=177047925916) (by decide) source088_valid tests56_088_0 fee56_088_21880 (by decide +kernel)

private theorem tests56_083_2529 : ∀ z∈source083.plan.table,z.1.Valid 56 2529 := by decide +kernel
private theorem fee56_083_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source083.plan.table+
      4*21880*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*228515839973 := by decide +kernel
private theorem range56From21487To2562 : Segment 56 21487 21880 2529 2562 :=
  paid (pc:=76) (v:=228515839973) (by decide) source083_valid tests56_083_2529 fee56_083_21880 (by decide +kernel)

private theorem tests56_091_2562 : ∀ z∈source091.plan.table,z.1.Valid 56 2562 := by decide +kernel
private theorem fee56_091_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source091.plan.table+
      4*21880*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*271499689088 := by decide +kernel
private theorem range56From21487To2645 : Segment 56 21487 21880 2562 2645 :=
  paid (pc:=75) (v:=271499689088) (by decide) source091_valid tests56_091_2562 fee56_091_21880 (by decide +kernel)

private theorem tests56_089_2645 : ∀ z∈source089.plan.table,z.1.Valid 56 2645 := by decide +kernel
private theorem fee56_089_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source089.plan.table+
      4*21880*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*261732503293 := by decide +kernel
private theorem range56From21487To2718 : Segment 56 21487 21880 2645 2718 :=
  paid (pc:=75) (v:=261732503293) (by decide) source089_valid tests56_089_2645 fee56_089_21880 (by decide +kernel)

private theorem tests56_089_2718 : ∀ z∈source089.plan.table,z.1.Valid 56 2718 := by decide +kernel
private theorem range56From21487To2720 : Segment 56 21487 21880 2718 2720 :=
  paid (pc:=75) (v:=261732503293) (by decide) source089_valid tests56_089_2718 fee56_089_21880 (by decide +kernel)

private theorem tests56_085_2720 : ∀ z∈source085.plan.table,z.1.Valid 56 2720 := by decide +kernel
private theorem fee56_085_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source085.plan.table+
      4*21880*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*251395989207 := by decide +kernel
private theorem range56From21487To2795 : Segment 56 21487 21880 2720 2795 :=
  paid (pc:=74) (v:=251395989207) (by decide) source085_valid tests56_085_2720 fee56_085_21880 (by decide +kernel)

private theorem tests56_092_2795 : ∀ z∈source092.plan.table,z.1.Valid 56 2795 := by decide +kernel
private theorem fee56_092_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source092.plan.table+
      4*21880*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*234157909864 := by decide +kernel
private theorem range56From21487To2926 : Segment 56 21487 21880 2795 2926 :=
  paid (pc:=73) (v:=234157909864) (by decide) source092_valid tests56_092_2795 fee56_092_21880 (by decide +kernel)

private theorem tests56_090_2926 : ∀ z∈source090.plan.table,z.1.Valid 56 2926 := by decide +kernel
private theorem fee56_090_21880 :
    PopulationFees20258.bill (n:=21880) (PopulationFees20258.tabulate (21880-1) 256) source090.plan.table+
      4*21880*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*215236826591 := by decide +kernel
private theorem range56From21487To3080 : Segment 56 21487 21880 2926 3080 :=
  paid (pc:=72) (v:=215236826591) (by decide) source090_valid tests56_090_2926 fee56_090_21880 (by decide +kernel)

private theorem tests56_090_3080 : ∀ z∈source090.plan.table,z.1.Valid 56 3080 := by decide +kernel
private theorem range56From21487To3081 : Segment 56 21487 21880 3080 3081 :=
  paid (pc:=72) (v:=215236826591) (by decide) source090_valid tests56_090_3080 fee56_090_21880 (by decide +kernel)

private theorem range56From21487 : Win 56 21487 21880 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range56From21487To2529 range56From21487To2562) (join_population range56From21487To2645 range56From21487To2718)) (join_population (join_population range56From21487To2720 range56From21487To2795) (join_population range56From21487To2926 (join_population range56From21487To3080 range56From21487To3081))))

private theorem fee56_088_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source088.plan.table+
      4*22284*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*183085623500 := by decide +kernel
private theorem range56From21881To2553 : Segment 56 21881 22284 0 2553 :=
  paid (pc:=76) (v:=183085623500) (by decide) source088_valid tests56_088_0 fee56_088_22284 (by decide +kernel)

private theorem tests56_091_2553 : ∀ z∈source091.plan.table,z.1.Valid 56 2553 := by decide +kernel
private theorem fee56_091_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source091.plan.table+
      4*22284*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*280647773424 := by decide +kernel
private theorem range56From21881To2662 : Segment 56 21881 22284 2553 2662 :=
  paid (pc:=76) (v:=280647773424) (by decide) source091_valid tests56_091_2553 fee56_091_22284 (by decide +kernel)

private theorem tests56_089_2662 : ∀ z∈source089.plan.table,z.1.Valid 56 2662 := by decide +kernel
private theorem fee56_089_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source089.plan.table+
      4*22284*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*270566125062 := by decide +kernel
private theorem range56From21881To2732 : Segment 56 21881 22284 2662 2732 :=
  paid (pc:=75) (v:=270566125062) (by decide) source089_valid tests56_089_2662 fee56_089_22284 (by decide +kernel)

private theorem tests56_085_2732 : ∀ z∈source085.plan.table,z.1.Valid 56 2732 := by decide +kernel
private theorem fee56_085_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source085.plan.table+
      4*22284*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*259974189634 := by decide +kernel
private theorem range56From21881To2805 : Segment 56 21881 22284 2732 2805 :=
  paid (pc:=74) (v:=259974189634) (by decide) source085_valid tests56_085_2732 fee56_085_22284 (by decide +kernel)

private theorem tests56_092_2805 : ∀ z∈source092.plan.table,z.1.Valid 56 2805 := by decide +kernel
private theorem fee56_092_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source092.plan.table+
      4*22284*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*242096609279 := by decide +kernel
private theorem range56From21881To2931 : Segment 56 21881 22284 2805 2931 :=
  paid (pc:=73) (v:=242096609279) (by decide) source092_valid tests56_092_2805 fee56_092_22284 (by decide +kernel)

private theorem tests56_090_2931 : ∀ z∈source090.plan.table,z.1.Valid 56 2931 := by decide +kernel
private theorem fee56_090_22284 :
    PopulationFees20258.bill (n:=22284) (PopulationFees20258.tabulate (22284-1) 256) source090.plan.table+
      4*22284*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*222586797061 := by decide +kernel
private theorem range56From21881To3077 : Segment 56 21881 22284 2931 3077 :=
  paid (pc:=72) (v:=222586797061) (by decide) source090_valid tests56_090_2931 fee56_090_22284 (by decide +kernel)

private theorem tests56_090_3077 : ∀ z∈source090.plan.table,z.1.Valid 56 3077 := by decide +kernel
private theorem range56From21881To3081 : Segment 56 21881 22284 3077 3081 :=
  paid (pc:=72) (v:=222586797061) (by decide) source090_valid tests56_090_3077 fee56_090_22284 (by decide +kernel)

private theorem range56From21881 : Win 56 21881 22284 :=
  complete (by decide) (by decide) (join_population (join_population range56From21881To2553 (join_population range56From21881To2662 range56From21881To2732)) (join_population (join_population range56From21881To2805 range56From21881To2931) (join_population range56From21881To3077 range56From21881To3081)))

private theorem fee56_088_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source088.plan.table+
      4*22698*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*189418085819 := by decide +kernel
private theorem range56From22285To2580 : Segment 56 22285 22698 0 2580 :=
  paid (pc:=77) (v:=189418085819) (by decide) source088_valid tests56_088_0 fee56_088_22698 (by decide +kernel)

private theorem tests56_091_2580 : ∀ z∈source091.plan.table,z.1.Valid 56 2580 := by decide +kernel
private theorem fee56_091_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source091.plan.table+
      4*22698*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*290209192609 := by decide +kernel
private theorem range56From22285To2681 : Segment 56 22285 22698 2580 2681 :=
  paid (pc:=76) (v:=290209192609) (by decide) source091_valid tests56_091_2580 fee56_091_22698 (by decide +kernel)

private theorem tests56_089_2681 : ∀ z∈source089.plan.table,z.1.Valid 56 2681 := by decide +kernel
private theorem fee56_089_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source089.plan.table+
      4*22698*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*279796103554 := by decide +kernel
private theorem range56From22285To2748 : Segment 56 22285 22698 2681 2748 :=
  paid (pc:=75) (v:=279796103554) (by decide) source089_valid tests56_089_2681 fee56_089_22698 (by decide +kernel)

private theorem tests56_085_2748 : ∀ z∈source085.plan.table,z.1.Valid 56 2748 := by decide +kernel
private theorem fee56_085_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source085.plan.table+
      4*22698*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*268858716382 := by decide +kernel
private theorem range56From22285To2819 : Segment 56 22285 22698 2748 2819 :=
  paid (pc:=75) (v:=268858716382) (by decide) source085_valid tests56_085_2748 fee56_085_22698 (by decide +kernel)

private theorem tests56_092_2819 : ∀ z∈source092.plan.table,z.1.Valid 56 2819 := by decide +kernel
private theorem fee56_092_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source092.plan.table+
      4*22698*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*250417293795 := by decide +kernel
private theorem range56From22285To2940 : Segment 56 22285 22698 2819 2940 :=
  paid (pc:=74) (v:=250417293795) (by decide) source092_valid tests56_092_2819 fee56_092_22698 (by decide +kernel)

private theorem tests56_090_2940 : ∀ z∈source090.plan.table,z.1.Valid 56 2940 := by decide +kernel
private theorem fee56_090_22698 :
    PopulationFees20258.bill (n:=22698) (PopulationFees20258.tabulate (22698-1) 256) source090.plan.table+
      4*22698*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*230262291040 := by decide +kernel
private theorem range56From22285To3078 : Segment 56 22285 22698 2940 3078 :=
  paid (pc:=73) (v:=230262291040) (by decide) source090_valid tests56_090_2940 fee56_090_22698 (by decide +kernel)

private theorem tests56_090_3078 : ∀ z∈source090.plan.table,z.1.Valid 56 3078 := by decide +kernel
private theorem range56From22285To3081 : Segment 56 22285 22698 3078 3081 :=
  paid (pc:=73) (v:=230262291040) (by decide) source090_valid tests56_090_3078 fee56_090_22698 (by decide +kernel)

private theorem range56From22285 : Win 56 22285 22698 :=
  complete (by decide) (by decide) (join_population (join_population range56From22285To2580 (join_population range56From22285To2681 range56From22285To2748)) (join_population (join_population range56From22285To2819 range56From22285To2940) (join_population range56From22285To3078 range56From22285To3081)))

theorem cut56From21487 : Win 56 21487 22698 :=
  (join_ground range56From21487 (join_ground range56From21881 range56From22285))

end JSP233.FiniteCutRanges20258
