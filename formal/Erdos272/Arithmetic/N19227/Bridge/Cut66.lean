module

public import Erdos272.Arithmetic.N20258.Sources.Source117
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee150At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source117.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source117.extras≤PopulationSources20258.source117.plan.scale*187998797421 := by decide +kernel
private theorem from19683To4291 : Segment 66 19683 20257 0 4291 :=
  paid (pc:=0) (v:=187998797421) (by decide) PopulationSources20258.source117_valid (by decide +kernel) fee150At20257 (by decide +kernel)

private theorem range19683 : Win 66 19683 20257 :=
  complete (by decide) (by decide) from19683To4291

theorem bridge66 : Win 66 19683 20257 :=
  range19683

end JSP233.Credit19227
