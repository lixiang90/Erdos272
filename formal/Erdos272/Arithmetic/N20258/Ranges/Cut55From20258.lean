module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source075
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source084
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source082.plan.table+
      4*20496*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*126780879731 := by decide +kernel
private theorem range55From20258To2396 : Segment 55 20258 20496 0 2396 :=
  paid (pc:=77) (v:=126780879731) (by decide) source082_valid tests55_082_0 fee55_082_20496 (by decide +kernel)

private theorem tests55_075_2396 : ∀ z∈source075.plan.table,z.1.Valid 55 2396 := by decide +kernel
private theorem fee55_075_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source075.plan.table+
      4*20496*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*170664356773 := by decide +kernel
private theorem range55From20258To2439 : Segment 55 20258 20496 2396 2439 :=
  paid (pc:=77) (v:=170664356773) (by decide) source075_valid tests55_075_2396 fee55_075_20496 (by decide +kernel)

private theorem tests55_084_2439 : ∀ z∈source084.plan.table,z.1.Valid 55 2439 := by decide +kernel
private theorem fee55_084_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source084.plan.table+
      4*20496*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*210089219889 := by decide +kernel
private theorem range55From20258To2510 : Segment 55 20258 20496 2439 2510 :=
  paid (pc:=76) (v:=210089219889) (by decide) source084_valid tests55_084_2439 fee55_084_20496 (by decide +kernel)

private theorem tests55_083_2510 : ∀ z∈source083.plan.table,z.1.Valid 55 2510 := by decide +kernel
private theorem fee55_083_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source083.plan.table+
      4*20496*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*202923454495 := by decide +kernel
private theorem range55From20258To2565 : Segment 55 20258 20496 2510 2565 :=
  paid (pc:=76) (v:=202923454495) (by decide) source083_valid tests55_083_2510 fee55_083_20496 (by decide +kernel)

private theorem tests55_083_2565 : ∀ z∈source083.plan.table,z.1.Valid 55 2565 := by decide +kernel
private theorem range55From20258To2566 : Segment 55 20258 20496 2565 2566 :=
  paid (pc:=76) (v:=202923454495) (by decide) source083_valid tests55_083_2565 fee55_083_20496 (by decide +kernel)

private theorem tests55_086_2566 : ∀ z∈source086.plan.table,z.1.Valid 55 2566 := by decide +kernel
private theorem fee55_086_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source086.plan.table+
      4*20496*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*241765621790 := by decide +kernel
private theorem range55From20258To2681 : Segment 55 20258 20496 2566 2681 :=
  paid (pc:=74) (v:=241765621790) (by decide) source086_valid tests55_086_2566 fee55_086_20496 (by decide +kernel)

private theorem tests55_085_2681 : ∀ z∈source085.plan.table,z.1.Valid 55 2681 := by decide +kernel
private theorem fee55_085_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source085.plan.table+
      4*20496*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*223264803867 := by decide +kernel
private theorem range55From20258To2863 : Segment 55 20258 20496 2681 2863 :=
  paid (pc:=73) (v:=223264803867) (by decide) source085_valid tests55_085_2681 fee55_085_20496 (by decide +kernel)

private theorem tests55_080_2863 : ∀ z∈source080.plan.table,z.1.Valid 55 2863 := by decide +kernel
private theorem fee55_080_20496 :
    PopulationFees20258.bill (n:=20496) (PopulationFees20258.tabulate (20496-1) 256) source080.plan.table+
      4*20496*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*204791778032 := by decide +kernel
private theorem range55From20258To2971 : Segment 55 20258 20496 2863 2971 :=
  paid (pc:=72) (v:=204791778032) (by decide) source080_valid tests55_080_2863 fee55_080_20496 (by decide +kernel)

private theorem range55From20258 : Win 55 20258 20496 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range55From20258To2396 range55From20258To2439) (join_population range55From20258To2510 range55From20258To2565)) (join_population (join_population range55From20258To2566 range55From20258To2681) (join_population range55From20258To2863 range55From20258To2971)))

private theorem fee55_082_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source082.plan.table+
      4*20760*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*129804408893 := by decide +kernel
private theorem range55From20497To2406 : Segment 55 20497 20760 0 2406 :=
  paid (pc:=77) (v:=129804408893) (by decide) source082_valid tests55_082_0 fee55_082_20760 (by decide +kernel)

private theorem tests55_075_2406 : ∀ z∈source075.plan.table,z.1.Valid 55 2406 := by decide +kernel
private theorem fee55_075_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source075.plan.table+
      4*20760*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*174776575898 := by decide +kernel
private theorem range55From20497To2444 : Segment 55 20497 20760 2406 2444 :=
  paid (pc:=77) (v:=174776575898) (by decide) source075_valid tests55_075_2406 fee55_075_20760 (by decide +kernel)

private theorem tests55_084_2444 : ∀ z∈source084.plan.table,z.1.Valid 55 2444 := by decide +kernel
private theorem fee55_084_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source084.plan.table+
      4*20760*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*215022673856 := by decide +kernel
private theorem range55From20497To2511 : Segment 55 20497 20760 2444 2511 :=
  paid (pc:=76) (v:=215022673856) (by decide) source084_valid tests55_084_2444 fee55_084_20760 (by decide +kernel)

private theorem tests55_083_2511 : ∀ z∈source083.plan.table,z.1.Valid 55 2511 := by decide +kernel
private theorem fee55_083_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source083.plan.table+
      4*20760*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*207703269508 := by decide +kernel
private theorem range55From20497To2565 : Segment 55 20497 20760 2511 2565 :=
  paid (pc:=76) (v:=207703269508) (by decide) source083_valid tests55_083_2511 fee55_083_20760 (by decide +kernel)

private theorem range55From20497To2566 : Segment 55 20497 20760 2565 2566 :=
  paid (pc:=76) (v:=207703269508) (by decide) source083_valid tests55_083_2565 fee55_083_20760 (by decide +kernel)

private theorem fee55_086_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source086.plan.table+
      4*20760*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*247417855794 := by decide +kernel
private theorem range55From20497To2673 : Segment 55 20497 20760 2566 2673 :=
  paid (pc:=75) (v:=247417855794) (by decide) source086_valid tests55_086_2566 fee55_086_20760 (by decide +kernel)

private theorem tests55_086_2673 : ∀ z∈source086.plan.table,z.1.Valid 55 2673 := by decide +kernel
private theorem range55From20497To2677 : Segment 55 20497 20760 2673 2677 :=
  paid (pc:=75) (v:=247417855794) (by decide) source086_valid tests55_086_2673 fee55_086_20760 (by decide +kernel)

private theorem tests55_085_2677 : ∀ z∈source085.plan.table,z.1.Valid 55 2677 := by decide +kernel
private theorem fee55_085_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source085.plan.table+
      4*20760*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*228516381580 := by decide +kernel
private theorem range55From20497To2848 : Segment 55 20497 20760 2677 2848 :=
  paid (pc:=73) (v:=228516381580) (by decide) source085_valid tests55_085_2677 fee55_085_20760 (by decide +kernel)

private theorem tests55_080_2848 : ∀ z∈source080.plan.table,z.1.Valid 55 2848 := by decide +kernel
private theorem fee55_080_20760 :
    PopulationFees20258.bill (n:=20760) (PopulationFees20258.tabulate (20760-1) 256) source080.plan.table+
      4*20760*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*209748493748 := by decide +kernel
private theorem range55From20497To2971 : Segment 55 20497 20760 2848 2971 :=
  paid (pc:=72) (v:=209748493748) (by decide) source080_valid tests55_080_2848 fee55_080_20760 (by decide +kernel)

private theorem range55From20497 : Win 55 20497 20760 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range55From20497To2406 range55From20497To2444) (join_population range55From20497To2511 range55From20497To2565)) (join_population (join_population range55From20497To2566 range55From20497To2673) (join_population range55From20497To2677 (join_population range55From20497To2848 range55From20497To2971))))

theorem cut55From20258 : Win 55 20258 20760 :=
  (join_ground range55From20258 range55From20497)

end JSP233.FiniteCutRanges20258
