module

public import Erdos272.Arithmetic.N20258.Sources.Source113
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee89At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source113.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source113.extras≤PopulationSources20258.source113.plan.scale*191121504466 := by decide +kernel
private theorem from19683To4161 : Segment 65 19683 20257 0 4161 :=
  paid (pc:=0) (v:=191121504466) (by decide) PopulationSources20258.source113_valid (by decide +kernel) fee89At20257 (by decide +kernel)

private theorem range19683 : Win 65 19683 20257 :=
  complete (by decide) (by decide) from19683To4161

theorem bridge65 : Win 65 19683 20257 :=
  range19683

end JSP233.Credit19227
