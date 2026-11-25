module

public import Erdos272.Arithmetic.N19227.Sources.P0
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee0At19592 :
    PopulationFees20258.bill (n:=19592) (PopulationFees20258.tabulate (19592-1) 256) p0.plan.table+
      4*19592*NaturalPopulation20258.weights p0.extras≤p0.plan.scale*24360143137 := by decide +kernel
private theorem from19227To1805 : Segment 43 19227 19592 0 1805 :=
  paid (pc:=80) (v:=24360143137) (by decide) p0_valid (by decide +kernel) fee0At19592 (by decide +kernel)

private theorem from19227To1807 : Segment 43 19227 19592 1805 1807 :=
  paid (pc:=80) (v:=24360143137) (by decide) p0_valid (by decide +kernel) fee0At19592 (by decide +kernel)

private theorem range19227 : Win 43 19227 19592 :=
  complete (by decide) (by decide) (join_population from19227To1805 from19227To1807)

private theorem fee0At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) p0.plan.table+
      4*19682*NaturalPopulation20258.weights p0.extras≤p0.plan.scale*24593411698 := by decide +kernel
private theorem from19593To1807 : Segment 43 19593 19682 0 1807 :=
  paid (pc:=82) (v:=24593411698) (by decide) p0_valid (by decide +kernel) fee0At19682 (by decide +kernel)

private theorem range19593 : Win 43 19593 19682 :=
  complete (by decide) (by decide) from19593To1807

theorem cut43 : Win 43 19227 19682 :=
  (join_ground range19227 range19593)

end JSP233.Credit19227
