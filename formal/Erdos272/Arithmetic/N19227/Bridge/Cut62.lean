module

public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source110
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee87At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source110.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source110.extras≤PopulationSources20258.source110.plan.scale*163486824797 := by decide +kernel
private theorem from19683To3257 : Segment 62 19683 20257 0 3257 :=
  paid (pc:=66) (v:=163486824797) (by decide) PopulationSources20258.source110_valid (by decide +kernel) fee87At20257 (by decide +kernel)

private theorem fee84At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source106.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source106.extras≤PopulationSources20258.source106.plan.scale*250576735804 := by decide +kernel
private theorem from19683To3783 : Segment 62 19683 20257 3257 3783 :=
  paid (pc:=0) (v:=250576735804) (by decide) PopulationSources20258.source106_valid (by decide +kernel) fee84At20257 (by decide +kernel)

private theorem range19683 : Win 62 19683 20257 :=
  complete (by decide) (by decide) (join_population from19683To3257 from19683To3783)

theorem bridge62 : Win 62 19683 20257 :=
  range19683

end JSP233.Credit19227
