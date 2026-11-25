module

public import Erdos272.Arithmetic.N19227.Sources.P0
public import Erdos272.Arithmetic.N19227.Sources.P1
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee1At20064 :
    PopulationFees20258.bill (n:=20064) (PopulationFees20258.tabulate (20064-1) 256) JSP233.Credit19227.p1.plan.table+
      4*20064*NaturalPopulation20258.weights JSP233.Credit19227.p1.extras≤JSP233.Credit19227.p1.plan.scale*48849351270 := by decide +kernel
private theorem from19683To1891 : Segment 44 19683 20064 0 1891 :=
  paid (pc:=80) (v:=48849351270) (by decide) JSP233.Credit19227.p1_valid (by decide +kernel) fee1At20064 (by decide +kernel)

private theorem from19683To1893 : Segment 44 19683 20064 1891 1893 :=
  paid (pc:=80) (v:=48849351270) (by decide) JSP233.Credit19227.p1_valid (by decide +kernel) fee1At20064 (by decide +kernel)

private theorem range19683 : Win 44 19683 20064 :=
  complete (by decide) (by decide) (join_population from19683To1891 from19683To1893)

private theorem fee0At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) JSP233.Credit19227.p0.plan.table+
      4*20257*NaturalPopulation20258.weights JSP233.Credit19227.p0.extras≤JSP233.Credit19227.p0.plan.scale*26029728229 := by decide +kernel
private theorem from20065To1893 : Segment 44 20065 20257 0 1893 :=
  paid (pc:=77) (v:=26029728229) (by decide) JSP233.Credit19227.p0_valid (by decide +kernel) fee0At20257 (by decide +kernel)

private theorem range20065 : Win 44 20065 20257 :=
  complete (by decide) (by decide) from20065To1893

theorem bridge44 : Win 44 19683 20257 :=
  (join_ground range19683 range20065)

end JSP233.Credit19227
