module

public import Erdos272.Arithmetic.N19227.Sources.P92
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee92At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) p92.plan.table+
      4*19682*NaturalPopulation20258.weights p92.extras≤p92.plan.scale*26208188364 := by decide +kernel
private theorem from19227To1723 : Segment 42 19227 19682 0 1723 :=
  paid (pc:=80) (v:=26208188364) (by decide) p92_valid (by decide +kernel) fee92At19682 (by decide +kernel)

private theorem range19227 : Win 42 19227 19682 :=
  complete (by decide) (by decide) from19227To1723

theorem cut42 : Win 42 19227 19682 :=
  range19227

end JSP233.Credit19227
