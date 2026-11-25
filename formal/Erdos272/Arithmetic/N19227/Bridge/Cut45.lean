module

public import Erdos272.Arithmetic.N19227.Sources.P1
public import Erdos272.Arithmetic.N19227.Sources.P2
public import Erdos272.Arithmetic.N19227.Sources.P3
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee2At19893 :
    PopulationFees20258.bill (n:=19893) (PopulationFees20258.tabulate (19893-1) 256) JSP233.Credit19227.p2.plan.table+
      4*19893*NaturalPopulation20258.weights JSP233.Credit19227.p2.extras≤JSP233.Credit19227.p2.plan.scale*45072649713 := by decide +kernel
private theorem from19683To1940 : Segment 45 19683 19893 0 1940 :=
  paid (pc:=80) (v:=45072649713) (by decide) JSP233.Credit19227.p2_valid (by decide +kernel) fee2At19893 (by decide +kernel)

private theorem from19683To1945 : Segment 45 19683 19893 1940 1945 :=
  paid (pc:=80) (v:=45072649713) (by decide) JSP233.Credit19227.p2_valid (by decide +kernel) fee2At19893 (by decide +kernel)

private theorem fee3At19893 :
    PopulationFees20258.bill (n:=19893) (PopulationFees20258.tabulate (19893-1) 256) JSP233.Credit19227.p3.plan.table+
      4*19893*NaturalPopulation20258.weights JSP233.Credit19227.p3.extras≤JSP233.Credit19227.p3.plan.scale*135049798520 := by decide +kernel
private theorem from19683To1981 : Segment 45 19683 19893 1945 1981 :=
  paid (pc:=72) (v:=135049798520) (by decide) JSP233.Credit19227.p3_valid (by decide +kernel) fee3At19893 (by decide +kernel)

private theorem range19683 : Win 45 19683 19893 :=
  complete (by decide) (by decide) (join_population from19683To1940 (join_population from19683To1945 from19683To1981))

private theorem fee2At20184 :
    PopulationFees20258.bill (n:=20184) (PopulationFees20258.tabulate (20184-1) 256) JSP233.Credit19227.p2.plan.table+
      4*20184*NaturalPopulation20258.weights JSP233.Credit19227.p2.extras≤JSP233.Credit19227.p2.plan.scale*46344925899 := by decide +kernel
private theorem from19894To1941 : Segment 45 19894 20184 0 1941 :=
  paid (pc:=80) (v:=46344925899) (by decide) JSP233.Credit19227.p2_valid (by decide +kernel) fee2At20184 (by decide +kernel)

private theorem from19894To1945 : Segment 45 19894 20184 1941 1945 :=
  paid (pc:=80) (v:=46344925899) (by decide) JSP233.Credit19227.p2_valid (by decide +kernel) fee2At20184 (by decide +kernel)

private theorem fee3At20184 :
    PopulationFees20258.bill (n:=20184) (PopulationFees20258.tabulate (20184-1) 256) JSP233.Credit19227.p3.plan.table+
      4*20184*NaturalPopulation20258.weights JSP233.Credit19227.p3.extras≤JSP233.Credit19227.p3.plan.scale*138748140638 := by decide +kernel
private theorem from19894To1981 : Segment 45 19894 20184 1945 1981 :=
  paid (pc:=72) (v:=138748140638) (by decide) JSP233.Credit19227.p3_valid (by decide +kernel) fee3At20184 (by decide +kernel)

private theorem range19894 : Win 45 19894 20184 :=
  complete (by decide) (by decide) (join_population from19894To1941 (join_population from19894To1945 from19894To1981))

private theorem fee1At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) JSP233.Credit19227.p1.plan.table+
      4*20257*NaturalPopulation20258.weights JSP233.Credit19227.p1.extras≤JSP233.Credit19227.p1.plan.scale*49797520485 := by decide +kernel
private theorem from20185To1981 : Segment 45 20185 20257 0 1981 :=
  paid (pc:=76) (v:=49797520485) (by decide) JSP233.Credit19227.p1_valid (by decide +kernel) fee1At20257 (by decide +kernel)

private theorem range20185 : Win 45 20185 20257 :=
  complete (by decide) (by decide) from20185To1981

theorem bridge45 : Win 45 19683 20257 :=
  (join_ground range19683 (join_ground range19894 range20185))

end JSP233.Credit19227
