module

public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee85At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source107.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source107.extras≤PopulationSources20258.source107.plan.scale*168579734270 := by decide +kernel
private theorem from19227To3213 : Segment 61 19227 19682 0 3213 :=
  paid (pc:=66) (v:=168579734270) (by decide) PopulationSources20258.source107_valid (by decide +kernel) fee85At19682 (by decide +kernel)

private theorem fee132At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source105.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source105.extras≤PopulationSources20258.source105.plan.scale*233249714084 := by decide +kernel
private theorem from19227To3661 : Segment 61 19227 19682 3213 3661 :=
  paid (pc:=60) (v:=233249714084) (by decide) PopulationSources20258.source105_valid (by decide +kernel) fee132At19682 (by decide +kernel)

private theorem range19227 : Win 61 19227 19682 :=
  complete (by decide) (by decide) (join_population from19227To3213 from19227To3661)

theorem cut61 : Win 61 19227 19682 :=
  range19227

end JSP233.Credit19227
