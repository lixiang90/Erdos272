module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source046
public import Erdos272.Arithmetic.N20258.Sources.Source047
public import Erdos272.Arithmetic.N20258.Sources.Source051
public import Erdos272.Arithmetic.N20258.Sources.Source052
public import Erdos272.Arithmetic.N20258.Sources.Source054
public import Erdos272.Arithmetic.N20258.Sources.Source055
public import Erdos272.Arithmetic.N20258.Sources.Source056

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests52_047_0 : ∀ z∈source047.plan.table,z.1.Valid 52 0 := by decide +kernel
private theorem fee52_047_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source047.plan.table+
      4*25777*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*167114635886 := by decide +kernel
private theorem range52From24726To2405 : Segment 52 24726 25777 0 2405 :=
  paid (pc:=77) (v:=167114635886) (by decide) source047_valid tests52_047_0 fee52_047_25777 (by decide +kernel)

private theorem tests52_051_2405 : ∀ z∈source051.plan.table,z.1.Valid 52 2405 := by decide +kernel
private theorem fee52_051_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source051.plan.table+
      4*25777*NaturalPopulation20258.weights source051.extras≤source051.plan.scale*264279538691 := by decide +kernel
private theorem range52From24726To2490 : Segment 52 24726 25777 2405 2490 :=
  paid (pc:=77) (v:=264279538691) (by decide) source051_valid tests52_051_2405 fee52_051_25777 (by decide +kernel)

private theorem tests52_052_2490 : ∀ z∈source052.plan.table,z.1.Valid 52 2490 := by decide +kernel
private theorem fee52_052_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source052.plan.table+
      4*25777*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*256841990903 := by decide +kernel
private theorem range52From24726To2515 : Segment 52 24726 25777 2490 2515 :=
  paid (pc:=76) (v:=256841990903) (by decide) source052_valid tests52_052_2490 fee52_052_25777 (by decide +kernel)

private theorem tests52_054_2515 : ∀ z∈source054.plan.table,z.1.Valid 52 2515 := by decide +kernel
private theorem fee52_054_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source054.plan.table+
      4*25777*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*308780039122 := by decide +kernel
private theorem range52From24726To2559 : Segment 52 24726 25777 2515 2559 :=
  paid (pc:=76) (v:=308780039122) (by decide) source054_valid tests52_054_2515 fee52_054_25777 (by decide +kernel)

private theorem tests52_046_2559 : ∀ z∈source046.plan.table,z.1.Valid 52 2559 := by decide +kernel
private theorem fee52_046_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source046.plan.table+
      4*25777*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*304047244732 := by decide +kernel
private theorem range52From24726To2577 : Segment 52 24726 25777 2559 2577 :=
  paid (pc:=76) (v:=304047244732) (by decide) source046_valid tests52_046_2559 fee52_046_25777 (by decide +kernel)

private theorem tests52_055_2577 : ∀ z∈source055.plan.table,z.1.Valid 52 2577 := by decide +kernel
private theorem fee52_055_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source055.plan.table+
      4*25777*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*289089595397 := by decide +kernel
private theorem range52From24726To2632 : Segment 52 24726 25777 2577 2632 :=
  paid (pc:=76) (v:=289089595397) (by decide) source055_valid tests52_055_2577 fee52_055_25777 (by decide +kernel)

private theorem tests52_056_2632 : ∀ z∈source056.plan.table,z.1.Valid 52 2632 := by decide +kernel
private theorem fee52_056_25777 :
    PopulationFees20258.bill (n:=25777) (PopulationFees20258.tabulate (25777-1) 256) source056.plan.table+
      4*25777*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*283856968451 := by decide +kernel
private theorem range52From24726To2653 : Segment 52 24726 25777 2632 2653 :=
  paid (pc:=76) (v:=283856968451) (by decide) source056_valid tests52_056_2632 fee52_056_25777 (by decide +kernel)

private theorem range52From24726 : Win 52 24726 25777 :=
  complete (by decide) (by decide) (join_population (join_population range52From24726To2405 (join_population range52From24726To2490 range52From24726To2515)) (join_population (join_population range52From24726To2559 range52From24726To2577) (join_population range52From24726To2632 range52From24726To2653)))

private theorem fee52_047_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source047.plan.table+
      4*27076*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*183211071373 := by decide +kernel
private theorem range52From25778To2436 : Segment 52 25778 27076 0 2436 :=
  paid (pc:=77) (v:=183211071373) (by decide) source047_valid tests52_047_0 fee52_047_27076 (by decide +kernel)

private theorem tests52_052_2436 : ∀ z∈source052.plan.table,z.1.Valid 52 2436 := by decide +kernel
private theorem fee52_052_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source052.plan.table+
      4*27076*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*281407450033 := by decide +kernel
private theorem range52From25778To2529 : Segment 52 25778 27076 2436 2529 :=
  paid (pc:=76) (v:=281407450033) (by decide) source052_valid tests52_052_2436 fee52_052_27076 (by decide +kernel)

private theorem tests52_054_2529 : ∀ z∈source054.plan.table,z.1.Valid 52 2529 := by decide +kernel
private theorem fee52_054_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source054.plan.table+
      4*27076*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*338208294175 := by decide +kernel
private theorem range52From25778To2564 : Segment 52 25778 27076 2529 2564 :=
  paid (pc:=76) (v:=338208294175) (by decide) source054_valid tests52_054_2529 fee52_054_27076 (by decide +kernel)

private theorem tests52_046_2564 : ∀ z∈source046.plan.table,z.1.Valid 52 2564 := by decide +kernel
private theorem fee52_046_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source046.plan.table+
      4*27076*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*333139850254 := by decide +kernel
private theorem range52From25778To2581 : Segment 52 25778 27076 2564 2581 :=
  paid (pc:=76) (v:=333139850254) (by decide) source046_valid tests52_046_2564 fee52_046_27076 (by decide +kernel)

private theorem tests52_055_2581 : ∀ z∈source055.plan.table,z.1.Valid 52 2581 := by decide +kernel
private theorem fee52_055_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source055.plan.table+
      4*27076*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*316729271650 := by decide +kernel
private theorem range52From25778To2634 : Segment 52 25778 27076 2581 2634 :=
  paid (pc:=76) (v:=316729271650) (by decide) source055_valid tests52_055_2581 fee52_055_27076 (by decide +kernel)

private theorem tests52_056_2634 : ∀ z∈source056.plan.table,z.1.Valid 52 2634 := by decide +kernel
private theorem fee52_056_27076 :
    PopulationFees20258.bill (n:=27076) (PopulationFees20258.tabulate (27076-1) 256) source056.plan.table+
      4*27076*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*311205877550 := by decide +kernel
private theorem range52From25778To2653 : Segment 52 25778 27076 2634 2653 :=
  paid (pc:=75) (v:=311205877550) (by decide) source056_valid tests52_056_2634 fee52_056_27076 (by decide +kernel)

private theorem range52From25778 : Win 52 25778 27076 :=
  complete (by decide) (by decide) (join_population (join_population range52From25778To2436 (join_population range52From25778To2529 range52From25778To2564)) (join_population range52From25778To2581 (join_population range52From25778To2634 range52From25778To2653)))

private theorem fee52_047_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source047.plan.table+
      4*28713*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*204571586015 := by decide +kernel
private theorem range52From27077To2469 : Segment 52 27077 28713 0 2469 :=
  paid (pc:=76) (v:=204571586015) (by decide) source047_valid tests52_047_0 fee52_047_28713 (by decide +kernel)

private theorem tests52_052_2469 : ∀ z∈source052.plan.table,z.1.Valid 52 2469 := by decide +kernel
private theorem fee52_052_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source052.plan.table+
      4*28713*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*313969309711 := by decide +kernel
private theorem range52From27077To2545 : Segment 52 27077 28713 2469 2545 :=
  paid (pc:=76) (v:=313969309711) (by decide) source052_valid tests52_052_2469 fee52_052_28713 (by decide +kernel)

private theorem tests52_054_2545 : ∀ z∈source054.plan.table,z.1.Valid 52 2545 := by decide +kernel
private theorem fee52_054_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source054.plan.table+
      4*28713*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*377224000231 := by decide +kernel
private theorem range52From27077To2569 : Segment 52 27077 28713 2545 2569 :=
  paid (pc:=76) (v:=377224000231) (by decide) source054_valid tests52_054_2545 fee52_054_28713 (by decide +kernel)

private theorem tests52_046_2569 : ∀ z∈source046.plan.table,z.1.Valid 52 2569 := by decide +kernel
private theorem fee52_046_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source046.plan.table+
      4*28713*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*371607335880 := by decide +kernel
private theorem range52From27077To2585 : Segment 52 27077 28713 2569 2585 :=
  paid (pc:=76) (v:=371607335880) (by decide) source046_valid tests52_046_2569 fee52_046_28713 (by decide +kernel)

private theorem tests52_055_2585 : ∀ z∈source055.plan.table,z.1.Valid 52 2585 := by decide +kernel
private theorem fee52_055_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source055.plan.table+
      4*28713*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*353371938150 := by decide +kernel
private theorem range52From27077To2635 : Segment 52 27077 28713 2585 2635 :=
  paid (pc:=75) (v:=353371938150) (by decide) source055_valid tests52_055_2585 fee52_055_28713 (by decide +kernel)

private theorem tests52_056_2635 : ∀ z∈source056.plan.table,z.1.Valid 52 2635 := by decide +kernel
private theorem fee52_056_28713 :
    PopulationFees20258.bill (n:=28713) (PopulationFees20258.tabulate (28713-1) 256) source056.plan.table+
      4*28713*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*347473059251 := by decide +kernel
private theorem range52From27077To2653 : Segment 52 27077 28713 2635 2653 :=
  paid (pc:=75) (v:=347473059251) (by decide) source056_valid tests52_056_2635 fee52_056_28713 (by decide +kernel)

private theorem range52From27077 : Win 52 27077 28713 :=
  complete (by decide) (by decide) (join_population (join_population range52From27077To2469 (join_population range52From27077To2545 range52From27077To2569)) (join_population range52From27077To2585 (join_population range52From27077To2635 range52From27077To2653)))

private theorem fee52_047_30824 :
    PopulationFees20258.bill (n:=30824) (PopulationFees20258.tabulate (30824-1) 256) source047.plan.table+
      4*30824*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*233785035818 := by decide +kernel
private theorem range52From28714To2505 : Segment 52 28714 30824 0 2505 :=
  paid (pc:=76) (v:=233785035818) (by decide) source047_valid tests52_047_0 fee52_047_30824 (by decide +kernel)

private theorem tests52_054_2505 : ∀ z∈source054.plan.table,z.1.Valid 52 2505 := by decide +kernel
private theorem fee52_054_30824 :
    PopulationFees20258.bill (n:=30824) (PopulationFees20258.tabulate (30824-1) 256) source054.plan.table+
      4*30824*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*430565442347 := by decide +kernel
private theorem range52From28714To2574 : Segment 52 28714 30824 2505 2574 :=
  paid (pc:=75) (v:=430565442347) (by decide) source054_valid tests52_054_2505 fee52_054_30824 (by decide +kernel)

private theorem tests52_046_2574 : ∀ z∈source046.plan.table,z.1.Valid 52 2574 := by decide +kernel
private theorem fee52_046_30824 :
    PopulationFees20258.bill (n:=30824) (PopulationFees20258.tabulate (30824-1) 256) source046.plan.table+
      4*30824*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*424321892675 := by decide +kernel
private theorem range52From28714To2589 : Segment 52 28714 30824 2574 2589 :=
  paid (pc:=75) (v:=424321892675) (by decide) source046_valid tests52_046_2574 fee52_046_30824 (by decide +kernel)

private theorem tests52_055_2589 : ∀ z∈source055.plan.table,z.1.Valid 52 2589 := by decide +kernel
private theorem fee52_055_30824 :
    PopulationFees20258.bill (n:=30824) (PopulationFees20258.tabulate (30824-1) 256) source055.plan.table+
      4*30824*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*403470361110 := by decide +kernel
private theorem range52From28714To2637 : Segment 52 28714 30824 2589 2637 :=
  paid (pc:=75) (v:=403470361110) (by decide) source055_valid tests52_055_2589 fee52_055_30824 (by decide +kernel)

private theorem tests52_056_2637 : ∀ z∈source056.plan.table,z.1.Valid 52 2637 := by decide +kernel
private theorem fee52_056_30824 :
    PopulationFees20258.bill (n:=30824) (PopulationFees20258.tabulate (30824-1) 256) source056.plan.table+
      4*30824*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*397047075836 := by decide +kernel
private theorem range52From28714To2653 : Segment 52 28714 30824 2637 2653 :=
  paid (pc:=75) (v:=397047075836) (by decide) source056_valid tests52_056_2637 fee52_056_30824 (by decide +kernel)

private theorem range52From28714 : Win 52 28714 30824 :=
  complete (by decide) (by decide) (join_population (join_population range52From28714To2505 range52From28714To2574) (join_population range52From28714To2589 (join_population range52From28714To2637 range52From28714To2653)))

theorem cut52From24726 : Win 52 24726 30824 :=
  (join_ground (join_ground range52From24726 range52From25778) (join_ground range52From27077 range52From28714))

end JSP233.FiniteCutRanges20258
