module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source046
public import Erdos272.Arithmetic.N20258.Sources.Source047
public import Erdos272.Arithmetic.N20258.Sources.Source050
public import Erdos272.Arithmetic.N20258.Sources.Source051
public import Erdos272.Arithmetic.N20258.Sources.Source052
public import Erdos272.Arithmetic.N20258.Sources.Source053
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
private theorem fee52_047_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source047.plan.table+
      4*23144*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*136703413519 := by decide +kernel
private theorem range52From22540To2334 : Segment 52 22540 23144 0 2334 :=
  paid (pc:=78) (v:=136703413519) (by decide) source047_valid tests52_047_0 fee52_047_23144 (by decide +kernel)

private theorem tests52_050_2334 : ∀ z∈source050.plan.table,z.1.Valid 52 2334 := by decide +kernel
private theorem fee52_050_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source050.plan.table+
      4*23144*NaturalPopulation20258.weights source050.extras≤source050.plan.scale*224187702293 := by decide +kernel
private theorem range52From22540To2422 : Segment 52 22540 23144 2334 2422 :=
  paid (pc:=77) (v:=224187702293) (by decide) source050_valid tests52_050_2334 fee52_050_23144 (by decide +kernel)

private theorem tests52_052_2422 : ∀ z∈source052.plan.table,z.1.Valid 52 2422 := by decide +kernel
private theorem fee52_052_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source052.plan.table+
      4*23144*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*210426805861 := by decide +kernel
private theorem range52From22540To2485 : Segment 52 22540 23144 2422 2485 :=
  paid (pc:=77) (v:=210426805861) (by decide) source052_valid tests52_052_2422 fee52_052_23144 (by decide +kernel)

private theorem tests52_053_2485 : ∀ z∈source053.plan.table,z.1.Valid 52 2485 := by decide +kernel
private theorem fee52_053_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source053.plan.table+
      4*23144*NaturalPopulation20258.weights source053.extras≤source053.plan.scale*263741401525 := by decide +kernel
private theorem range52From22540To2501 : Segment 52 22540 23144 2485 2501 :=
  paid (pc:=77) (v:=263741401525) (by decide) source053_valid tests52_053_2485 fee52_053_23144 (by decide +kernel)

private theorem tests52_054_2501 : ∀ z∈source054.plan.table,z.1.Valid 52 2501 := by decide +kernel
private theorem fee52_054_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source054.plan.table+
      4*23144*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*253140618827 := by decide +kernel
private theorem range52From22540To2555 : Segment 52 22540 23144 2501 2555 :=
  paid (pc:=76) (v:=253140618827) (by decide) source054_valid tests52_054_2501 fee52_054_23144 (by decide +kernel)

private theorem tests52_046_2555 : ∀ z∈source046.plan.table,z.1.Valid 52 2555 := by decide +kernel
private theorem fee52_046_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source046.plan.table+
      4*23144*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*249190293914 := by decide +kernel
private theorem range52From22540To2577 : Segment 52 22540 23144 2555 2577 :=
  paid (pc:=76) (v:=249190293914) (by decide) source046_valid tests52_046_2555 fee52_046_23144 (by decide +kernel)

private theorem tests52_055_2577 : ∀ z∈source055.plan.table,z.1.Valid 52 2577 := by decide +kernel
private theorem fee52_055_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source055.plan.table+
      4*23144*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*236869391653 := by decide +kernel
private theorem range52From22540To2639 : Segment 52 22540 23144 2577 2639 :=
  paid (pc:=76) (v:=236869391653) (by decide) source055_valid tests52_055_2577 fee52_055_23144 (by decide +kernel)

private theorem tests52_056_2639 : ∀ z∈source056.plan.table,z.1.Valid 52 2639 := by decide +kernel
private theorem fee52_056_23144 :
    PopulationFees20258.bill (n:=23144) (PopulationFees20258.tabulate (23144-1) 256) source056.plan.table+
      4*23144*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*232255206290 := by decide +kernel
private theorem range52From22540To2653 : Segment 52 22540 23144 2639 2653 :=
  paid (pc:=75) (v:=232255206290) (by decide) source056_valid tests52_056_2639 fee52_056_23144 (by decide +kernel)

private theorem range52From22540 : Win 52 22540 23144 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range52From22540To2334 range52From22540To2422) (join_population range52From22540To2485 range52From22540To2501)) (join_population (join_population range52From22540To2555 range52From22540To2577) (join_population range52From22540To2639 range52From22540To2653)))

private theorem fee52_047_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source047.plan.table+
      4*23862*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*144719513091 := by decide +kernel
private theorem range52From23145To2355 : Segment 52 23145 23862 0 2355 :=
  paid (pc:=78) (v:=144719513091) (by decide) source047_valid tests52_047_0 fee52_047_23862 (by decide +kernel)

private theorem tests52_050_2355 : ∀ z∈source050.plan.table,z.1.Valid 52 2355 := by decide +kernel
private theorem fee52_050_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source050.plan.table+
      4*23862*NaturalPopulation20258.weights source050.extras≤source050.plan.scale*237171069710 := by decide +kernel
private theorem range52From23145To2434 : Segment 52 23145 23862 2355 2434 :=
  paid (pc:=77) (v:=237171069710) (by decide) source050_valid tests52_050_2355 fee52_050_23862 (by decide +kernel)

private theorem tests52_052_2434 : ∀ z∈source052.plan.table,z.1.Valid 52 2434 := by decide +kernel
private theorem fee52_052_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source052.plan.table+
      4*23862*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*222658258648 := by decide +kernel
private theorem range52From23145To2494 : Segment 52 23145 23862 2434 2494 :=
  paid (pc:=77) (v:=222658258648) (by decide) source052_valid tests52_052_2434 fee52_052_23862 (by decide +kernel)

private theorem tests52_054_2494 : ∀ z∈source054.plan.table,z.1.Valid 52 2494 := by decide +kernel
private theorem fee52_054_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source054.plan.table+
      4*23862*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*267797956466 := by decide +kernel
private theorem range52From23145To2554 : Segment 52 23145 23862 2494 2554 :=
  paid (pc:=76) (v:=267797956466) (by decide) source054_valid tests52_054_2494 fee52_054_23862 (by decide +kernel)

private theorem tests52_046_2554 : ∀ z∈source046.plan.table,z.1.Valid 52 2554 := by decide +kernel
private theorem fee52_046_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source046.plan.table+
      4*23862*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*263421567703 := by decide +kernel
private theorem range52From23145To2577 : Segment 52 23145 23862 2554 2577 :=
  paid (pc:=76) (v:=263421567703) (by decide) source046_valid tests52_046_2554 fee52_046_23862 (by decide +kernel)

private theorem fee52_055_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source055.plan.table+
      4*23862*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*250628525884 := by decide +kernel
private theorem range52From23145To2636 : Segment 52 23145 23862 2577 2636 :=
  paid (pc:=76) (v:=250628525884) (by decide) source055_valid tests52_055_2577 fee52_055_23862 (by decide +kernel)

private theorem tests52_056_2636 : ∀ z∈source056.plan.table,z.1.Valid 52 2636 := by decide +kernel
private theorem fee52_056_23862 :
    PopulationFees20258.bill (n:=23862) (PopulationFees20258.tabulate (23862-1) 256) source056.plan.table+
      4*23862*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*245880481678 := by decide +kernel
private theorem range52From23145To2653 : Segment 52 23145 23862 2636 2653 :=
  paid (pc:=75) (v:=245880481678) (by decide) source056_valid tests52_056_2636 fee52_056_23862 (by decide +kernel)

private theorem range52From23145 : Win 52 23145 23862 :=
  complete (by decide) (by decide) (join_population (join_population range52From23145To2355 (join_population range52From23145To2434 range52From23145To2494)) (join_population (join_population range52From23145To2554 range52From23145To2577) (join_population range52From23145To2636 range52From23145To2653)))

private theorem fee52_047_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source047.plan.table+
      4*24725*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*154572307474 := by decide +kernel
private theorem range52From23863To2379 : Segment 52 23863 24725 0 2379 :=
  paid (pc:=77) (v:=154572307474) (by decide) source047_valid tests52_047_0 fee52_047_24725 (by decide +kernel)

private theorem tests52_051_2379 : ∀ z∈source051.plan.table,z.1.Valid 52 2379 := by decide +kernel
private theorem fee52_051_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source051.plan.table+
      4*24725*NaturalPopulation20258.weights source051.extras≤source051.plan.scale*244607679681 := by decide +kernel
private theorem range52From23863To2477 : Segment 52 23863 24725 2379 2477 :=
  paid (pc:=77) (v:=244607679681) (by decide) source051_valid tests52_051_2379 fee52_051_24725 (by decide +kernel)

private theorem tests52_053_2477 : ∀ z∈source053.plan.table,z.1.Valid 52 2477 := by decide +kernel
private theorem fee52_053_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source053.plan.table+
      4*24725*NaturalPopulation20258.weights source053.extras≤source053.plan.scale*297754902901 := by decide +kernel
private theorem range52From23863To2507 : Segment 52 23863 24725 2477 2507 :=
  paid (pc:=77) (v:=297754902901) (by decide) source053_valid tests52_053_2477 fee52_053_24725 (by decide +kernel)

private theorem tests52_054_2507 : ∀ z∈source054.plan.table,z.1.Valid 52 2507 := by decide +kernel
private theorem fee52_054_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source054.plan.table+
      4*24725*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*285838131883 := by decide +kernel
private theorem range52From23863To2557 : Segment 52 23863 24725 2507 2557 :=
  paid (pc:=76) (v:=285838131883) (by decide) source054_valid tests52_054_2507 fee52_054_24725 (by decide +kernel)

private theorem tests52_046_2557 : ∀ z∈source046.plan.table,z.1.Valid 52 2557 := by decide +kernel
private theorem fee52_046_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source046.plan.table+
      4*24725*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*281417353620 := by decide +kernel
private theorem range52From23863To2577 : Segment 52 23863 24725 2557 2577 :=
  paid (pc:=76) (v:=281417353620) (by decide) source046_valid tests52_046_2557 fee52_046_24725 (by decide +kernel)

private theorem fee52_055_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source055.plan.table+
      4*24725*NaturalPopulation20258.weights source055.extras≤source055.plan.scale*267563450022 := by decide +kernel
private theorem range52From23863To2634 : Segment 52 23863 24725 2577 2634 :=
  paid (pc:=76) (v:=267563450022) (by decide) source055_valid tests52_055_2577 fee52_055_24725 (by decide +kernel)

private theorem tests52_056_2634 : ∀ z∈source056.plan.table,z.1.Valid 52 2634 := by decide +kernel
private theorem fee52_056_24725 :
    PopulationFees20258.bill (n:=24725) (PopulationFees20258.tabulate (24725-1) 256) source056.plan.table+
      4*24725*NaturalPopulation20258.weights source056.extras≤source056.plan.scale*262599688619 := by decide +kernel
private theorem range52From23863To2653 : Segment 52 23863 24725 2634 2653 :=
  paid (pc:=76) (v:=262599688619) (by decide) source056_valid tests52_056_2634 fee52_056_24725 (by decide +kernel)

private theorem range52From23863 : Win 52 23863 24725 :=
  complete (by decide) (by decide) (join_population (join_population range52From23863To2379 (join_population range52From23863To2477 range52From23863To2507)) (join_population (join_population range52From23863To2557 range52From23863To2577) (join_population range52From23863To2634 range52From23863To2653)))

theorem cut52From22540 : Win 52 22540 24725 :=
  (join_ground range52From22540 (join_ground range52From23145 range52From23863))

end JSP233.FiniteCutRanges20258
