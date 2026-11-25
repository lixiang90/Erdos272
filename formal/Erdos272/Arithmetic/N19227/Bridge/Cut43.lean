module

public import Erdos272.Arithmetic.N19227.Sources.P0
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee0At20240 :
    PopulationFees20258.bill (n:=20240) (PopulationFees20258.tabulate (20240-1) 256) JSP233.Credit19227.p0.plan.table+
      4*20240*NaturalPopulation20258.weights JSP233.Credit19227.p0.extras≤JSP233.Credit19227.p0.plan.scale*25952993268 := by decide +kernel
private theorem from19683To1806 : Segment 43 19683 20240 0 1806 :=
  paid (pc:=79) (v:=25952993268) (by decide) JSP233.Credit19227.p0_valid (by decide +kernel) fee0At20240 (by decide +kernel)

private theorem from19683To1807 : Segment 43 19683 20240 1806 1807 :=
  paid (pc:=79) (v:=25952993268) (by decide) JSP233.Credit19227.p0_valid (by decide +kernel) fee0At20240 (by decide +kernel)

private theorem range19683 : Win 43 19683 20240 :=
  complete (by decide) (by decide) (join_population from19683To1806 from19683To1807)

private theorem fee0At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) JSP233.Credit19227.p0.plan.table+
      4*20257*NaturalPopulation20258.weights JSP233.Credit19227.p0.extras≤JSP233.Credit19227.p0.plan.scale*26029728229 := by decide +kernel
private theorem from20241To1807 : Segment 43 20241 20257 0 1807 :=
  paid (pc:=69) (v:=26029728229) (by decide) JSP233.Credit19227.p0_valid (by decide +kernel) fee0At20257 (by decide +kernel)

private theorem range20241 : Win 43 20241 20257 :=
  complete (by decide) (by decide) from20241To1807

theorem bridge43 : Win 43 19683 20257 :=
  (join_ground range19683 range20241)

end JSP233.Credit19227
