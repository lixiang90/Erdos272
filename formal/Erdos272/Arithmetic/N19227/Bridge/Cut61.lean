module

public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee85At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source107.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source107.extras≤PopulationSources20258.source107.plan.scale*177597742638 := by decide +kernel
private theorem from19683To3064 : Segment 61 19683 20257 0 3064 :=
  paid (pc:=68) (v:=177597742638) (by decide) PopulationSources20258.source107_valid (by decide +kernel) fee85At20257 (by decide +kernel)

private theorem fee146At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source102.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source102.extras≤PopulationSources20258.source102.plan.scale*219119737671 := by decide +kernel
private theorem from19683To3584 : Segment 61 19683 20257 3064 3584 :=
  paid (pc:=63) (v:=219119737671) (by decide) PopulationSources20258.source102_valid (by decide +kernel) fee146At20257 (by decide +kernel)

private theorem fee84At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source106.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source106.extras≤PopulationSources20258.source106.plan.scale*250576735804 := by decide +kernel
private theorem from19683To3661 : Segment 61 19683 20257 3584 3661 :=
  paid (pc:=0) (v:=250576735804) (by decide) PopulationSources20258.source106_valid (by decide +kernel) fee84At20257 (by decide +kernel)

private theorem range19683 : Win 61 19683 20257 :=
  complete (by decide) (by decide) (join_population from19683To3064 (join_population from19683To3584 from19683To3661))

theorem bridge61 : Win 61 19683 20257 :=
  range19683

end JSP233.Credit19227
