module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source078
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source084
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086
public import Erdos272.Arithmetic.N20258.Sources.Source087

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source082.plan.table+
      4*22080*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*145454227181 := by decide +kernel
private theorem range55From21699To2458 : Segment 55 21699 22080 0 2458 :=
  paid (pc:=77) (v:=145454227181) (by decide) source082_valid tests55_082_0 fee55_082_22080 (by decide +kernel)

private theorem tests55_084_2458 : ∀ z∈source084.plan.table,z.1.Valid 55 2458 := by decide +kernel
private theorem fee55_084_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source084.plan.table+
      4*22080*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*240478901839 := by decide +kernel
private theorem range55From21699To2535 : Segment 55 21699 22080 2458 2535 :=
  paid (pc:=77) (v:=240478901839) (by decide) source084_valid tests55_084_2458 fee55_084_22080 (by decide +kernel)

private theorem tests55_083_2535 : ∀ z∈source083.plan.table,z.1.Valid 55 2535 := by decide +kernel
private theorem fee55_083_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source083.plan.table+
      4*22080*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*232325277397 := by decide +kernel
private theorem range55From21699To2584 : Segment 55 21699 22080 2535 2584 :=
  paid (pc:=76) (v:=232325277397) (by decide) source083_valid tests55_083_2535 fee55_083_22080 (by decide +kernel)

private theorem tests55_086_2584 : ∀ z∈source086.plan.table,z.1.Valid 55 2584 := by decide +kernel
private theorem fee55_086_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source086.plan.table+
      4*22080*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*276621371944 := by decide +kernel
private theorem range55From21699To2662 : Segment 55 21699 22080 2584 2662 :=
  paid (pc:=76) (v:=276621371944) (by decide) source086_valid tests55_086_2584 fee55_086_22080 (by decide +kernel)

private theorem tests55_078_2662 : ∀ z∈source078.plan.table,z.1.Valid 55 2662 := by decide +kernel
private theorem fee55_078_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source078.plan.table+
      4*22080*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*216651605017 := by decide +kernel
private theorem range55From21699To2680 : Segment 55 21699 22080 2662 2680 :=
  paid (pc:=75) (v:=216651605017) (by decide) source078_valid tests55_078_2662 fee55_078_22080 (by decide +kernel)

private theorem tests55_085_2680 : ∀ z∈source085.plan.table,z.1.Valid 55 2680 := by decide +kernel
private theorem fee55_085_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source085.plan.table+
      4*22080*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*255579623303 := by decide +kernel
private theorem range55From21699To2812 : Segment 55 21699 22080 2680 2812 :=
  paid (pc:=74) (v:=255579623303) (by decide) source085_valid tests55_085_2680 fee55_085_22080 (by decide +kernel)

private theorem tests55_087_2812 : ∀ z∈source087.plan.table,z.1.Valid 55 2812 := by decide +kernel
private theorem fee55_087_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source087.plan.table+
      4*22080*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*237227577255 := by decide +kernel
private theorem range55From21699To2949 : Segment 55 21699 22080 2812 2949 :=
  paid (pc:=73) (v:=237227577255) (by decide) source087_valid tests55_087_2812 fee55_087_22080 (by decide +kernel)

private theorem tests55_080_2949 : ∀ z∈source080.plan.table,z.1.Valid 55 2949 := by decide +kernel
private theorem fee55_080_22080 :
    PopulationFees20258.bill (n:=22080) (PopulationFees20258.tabulate (22080-1) 256) source080.plan.table+
      4*22080*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*234683816767 := by decide +kernel
private theorem range55From21699To2971 : Segment 55 21699 22080 2949 2971 :=
  paid (pc:=73) (v:=234683816767) (by decide) source080_valid tests55_080_2949 fee55_080_22080 (by decide +kernel)

private theorem range55From21699 : Win 55 21699 22080 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range55From21699To2458 range55From21699To2535) (join_population range55From21699To2584 range55From21699To2662)) (join_population (join_population range55From21699To2680 range55From21699To2812) (join_population range55From21699To2949 range55From21699To2971)))

private theorem fee55_082_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source082.plan.table+
      4*22479*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*150448334248 := by decide +kernel
private theorem range55From22081To2481 : Segment 55 22081 22479 0 2481 :=
  paid (pc:=77) (v:=150448334248) (by decide) source082_valid tests55_082_0 fee55_082_22479 (by decide +kernel)

private theorem tests55_083_2481 : ∀ z∈source083.plan.table,z.1.Valid 55 2481 := by decide +kernel
private theorem fee55_083_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source083.plan.table+
      4*22479*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*240177867130 := by decide +kernel
private theorem range55From22081To2599 : Segment 55 22081 22479 2481 2599 :=
  paid (pc:=76) (v:=240177867130) (by decide) source083_valid tests55_083_2481 fee55_083_22479 (by decide +kernel)

private theorem tests55_086_2599 : ∀ z∈source086.plan.table,z.1.Valid 55 2599 := by decide +kernel
private theorem fee55_086_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source086.plan.table+
      4*22479*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*285924438528 := by decide +kernel
private theorem range55From22081To2676 : Segment 55 22081 22479 2599 2676 :=
  paid (pc:=76) (v:=285924438528) (by decide) source086_valid tests55_086_2599 fee55_086_22479 (by decide +kernel)

private theorem tests55_085_2676 : ∀ z∈source085.plan.table,z.1.Valid 55 2676 := by decide +kernel
private theorem fee55_085_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source085.plan.table+
      4*22479*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*264207533386 := by decide +kernel
private theorem range55From22081To2818 : Segment 55 22081 22479 2676 2818 :=
  paid (pc:=75) (v:=264207533386) (by decide) source085_valid tests55_085_2676 fee55_085_22479 (by decide +kernel)

private theorem tests55_087_2818 : ∀ z∈source087.plan.table,z.1.Valid 55 2818 := by decide +kernel
private theorem fee55_087_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source087.plan.table+
      4*22479*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*245276522578 := by decide +kernel
private theorem range55From22081To2949 : Segment 55 22081 22479 2818 2949 :=
  paid (pc:=74) (v:=245276522578) (by decide) source087_valid tests55_087_2818 fee55_087_22479 (by decide +kernel)

private theorem fee55_080_22479 :
    PopulationFees20258.bill (n:=22479) (PopulationFees20258.tabulate (22479-1) 256) source080.plan.table+
      4*22479*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*242627209604 := by decide +kernel
private theorem range55From22081To2971 : Segment 55 22081 22479 2949 2971 :=
  paid (pc:=73) (v:=242627209604) (by decide) source080_valid tests55_080_2949 fee55_080_22479 (by decide +kernel)

private theorem range55From22081 : Win 55 22081 22479 :=
  complete (by decide) (by decide) (join_population (join_population range55From22081To2481 (join_population range55From22081To2599 range55From22081To2676)) (join_population range55From22081To2818 (join_population range55From22081To2949 range55From22081To2971)))

private theorem fee55_082_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source082.plan.table+
      4*22902*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*155752315131 := by decide +kernel
private theorem range55From22480To2505 : Segment 55 22480 22902 0 2505 :=
  paid (pc:=77) (v:=155752315131) (by decide) source082_valid tests55_082_0 fee55_082_22902 (by decide +kernel)

private theorem tests55_083_2505 : ∀ z∈source083.plan.table,z.1.Valid 55 2505 := by decide +kernel
private theorem fee55_083_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source083.plan.table+
      4*22902*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*248507188321 := by decide +kernel
private theorem range55From22480To2618 : Segment 55 22480 22902 2505 2618 :=
  paid (pc:=77) (v:=248507188321) (by decide) source083_valid tests55_083_2505 fee55_083_22902 (by decide +kernel)

private theorem tests55_086_2618 : ∀ z∈source086.plan.table,z.1.Valid 55 2618 := by decide +kernel
private theorem fee55_086_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source086.plan.table+
      4*22902*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*295796349498 := by decide +kernel
private theorem range55From22480To2688 : Segment 55 22480 22902 2618 2688 :=
  paid (pc:=76) (v:=295796349498) (by decide) source086_valid tests55_086_2618 fee55_086_22902 (by decide +kernel)

private theorem tests55_085_2688 : ∀ z∈source085.plan.table,z.1.Valid 55 2688 := by decide +kernel
private theorem fee55_085_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source085.plan.table+
      4*22902*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*273363833450 := by decide +kernel
private theorem range55From22480To2825 : Segment 55 22480 22902 2688 2825 :=
  paid (pc:=75) (v:=273363833450) (by decide) source085_valid tests55_085_2688 fee55_085_22902 (by decide +kernel)

private theorem tests55_087_2825 : ∀ z∈source087.plan.table,z.1.Valid 55 2825 := by decide +kernel
private theorem fee55_087_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source087.plan.table+
      4*22902*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*253814584274 := by decide +kernel
private theorem range55From22480To2951 : Segment 55 22480 22902 2825 2951 :=
  paid (pc:=74) (v:=253814584274) (by decide) source087_valid tests55_087_2825 fee55_087_22902 (by decide +kernel)

private theorem tests55_080_2951 : ∀ z∈source080.plan.table,z.1.Valid 55 2951 := by decide +kernel
private theorem fee55_080_22902 :
    PopulationFees20258.bill (n:=22902) (PopulationFees20258.tabulate (22902-1) 256) source080.plan.table+
      4*22902*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*251159982123 := by decide +kernel
private theorem range55From22480To2971 : Segment 55 22480 22902 2951 2971 :=
  paid (pc:=74) (v:=251159982123) (by decide) source080_valid tests55_080_2951 fee55_080_22902 (by decide +kernel)

private theorem range55From22480 : Win 55 22480 22902 :=
  complete (by decide) (by decide) (join_population (join_population range55From22480To2505 (join_population range55From22480To2618 range55From22480To2688)) (join_population range55From22480To2825 (join_population range55From22480To2951 range55From22480To2971)))

theorem cut55From21699 : Win 55 21699 22902 :=
  (join_ground range55From21699 (join_ground range55From22081 range55From22480))

end JSP233.FiniteCutRanges20258
