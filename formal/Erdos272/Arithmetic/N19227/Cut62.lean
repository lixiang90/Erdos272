module

public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source110
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee87At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source110.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source110.extras≤PopulationSources20258.source110.plan.scale*155202701987 := by decide +kernel
private theorem from19227To3450 : Segment 62 19227 19682 0 3450 :=
  paid (pc:=64) (v:=155202701987) (by decide) PopulationSources20258.source110_valid (by decide +kernel) fee87At19682 (by decide +kernel)

private theorem fee132At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source105.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source105.extras≤PopulationSources20258.source105.plan.scale*233249714084 := by decide +kernel
private theorem from19227To3783 : Segment 62 19227 19682 3450 3783 :=
  paid (pc:=60) (v:=233249714084) (by decide) PopulationSources20258.source105_valid (by decide +kernel) fee132At19682 (by decide +kernel)

private theorem range19227 : Win 62 19227 19682 :=
  complete (by decide) (by decide) (join_population from19227To3450 from19227To3783)

theorem cut62 : Win 62 19227 19682 :=
  range19227

end JSP233.Credit19227
