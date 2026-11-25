module

public import Erdos272.Arithmetic.N20258.Sources.Source114
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee90At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source114.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source114.extras≤PopulationSources20258.source114.plan.scale*167563796432 := by decide +kernel
private theorem from19227To4033 : Segment 64 19227 19682 0 4033 :=
  paid (pc:=55) (v:=167563796432) (by decide) PopulationSources20258.source114_valid (by decide +kernel) fee90At19682 (by decide +kernel)

private theorem range19227 : Win 64 19227 19682 :=
  complete (by decide) (by decide) from19227To4033

theorem cut64 : Win 64 19227 19682 :=
  range19227

end JSP233.Credit19227
