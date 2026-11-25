module

public import Erdos272.Arithmetic.N20258.Sources.Source113
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee89At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source113.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source113.extras≤PopulationSources20258.source113.plan.scale*181420968315 := by decide +kernel
private theorem from19227To3907 : Segment 63 19227 19682 0 3907 :=
  paid (pc:=57) (v:=181420968315) (by decide) PopulationSources20258.source113_valid (by decide +kernel) fee89At19682 (by decide +kernel)

private theorem range19227 : Win 63 19227 19682 :=
  complete (by decide) (by decide) from19227To3907

theorem cut63 : Win 63 19227 19682 :=
  range19227

end JSP233.Credit19227
