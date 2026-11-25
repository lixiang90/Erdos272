module

public import Erdos272.Arithmetic.N19227.Sources.P1
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee1At19437 :
    PopulationFees20258.bill (n:=19437) (PopulationFees20258.tabulate (19437-1) 256) p1.plan.table+
      4*19437*NaturalPopulation20258.weights p1.extras≤p1.plan.scale*45979337772 := by decide +kernel
private theorem from19227To1889 : Segment 44 19227 19437 0 1889 :=
  paid (pc:=81) (v:=45979337772) (by decide) p1_valid (by decide +kernel) fee1At19437 (by decide +kernel)

private theorem from19227To1893 : Segment 44 19227 19437 1889 1893 :=
  paid (pc:=81) (v:=45979337772) (by decide) p1_valid (by decide +kernel) fee1At19437 (by decide +kernel)

private theorem range19227 : Win 44 19227 19437 :=
  complete (by decide) (by decide) (join_population from19227To1889 from19227To1893)

private theorem fee1At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) p1.plan.table+
      4*19682*NaturalPopulation20258.weights p1.extras≤p1.plan.scale*47112222961 := by decide +kernel
private theorem from19438To1893 : Segment 44 19438 19682 0 1893 :=
  paid (pc:=80) (v:=47112222961) (by decide) p1_valid (by decide +kernel) fee1At19682 (by decide +kernel)

private theorem range19438 : Win 44 19438 19682 :=
  complete (by decide) (by decide) from19438To1893

theorem cut44 : Win 44 19227 19682 :=
  (join_ground range19227 range19438)

end JSP233.Credit19227
