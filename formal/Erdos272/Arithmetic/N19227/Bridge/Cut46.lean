module

public import Erdos272.Arithmetic.N19227.Sources.P3
public import Erdos272.Arithmetic.N20258.Sources.Source001
public import Erdos272.Arithmetic.N20258.Sources.Source002
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee4At19894 :
    PopulationFees20258.bill (n:=19894) (PopulationFees20258.tabulate (19894-1) 256) PopulationSources20258.source001.plan.table+
      4*19894*NaturalPopulation20258.weights PopulationSources20258.source001.extras≤PopulationSources20258.source001.plan.scale*73496730917 := by decide +kernel
private theorem from19683To1978 : Segment 46 19683 19894 0 1978 :=
  paid (pc:=80) (v:=73496730917) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At19894 (by decide +kernel)

private theorem from19683To1983 : Segment 46 19683 19894 1978 1983 :=
  paid (pc:=80) (v:=73496730917) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At19894 (by decide +kernel)

private theorem from19683To1984 : Segment 46 19683 19894 1983 1984 :=
  paid (pc:=80) (v:=73496730917) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At19894 (by decide +kernel)

private theorem fee5At19894 :
    PopulationFees20258.bill (n:=19894) (PopulationFees20258.tabulate (19894-1) 256) PopulationSources20258.source002.plan.table+
      4*19894*NaturalPopulation20258.weights PopulationSources20258.source002.extras≤PopulationSources20258.source002.plan.scale*131333687954 := by decide +kernel
private theorem from19683To2071 : Segment 46 19683 19894 1984 2071 :=
  paid (pc:=77) (v:=131333687954) (by decide) PopulationSources20258.source002_valid (by decide +kernel) fee5At19894 (by decide +kernel)

private theorem range19683 : Win 46 19683 19894 :=
  complete (by decide) (by decide) (join_population (join_population from19683To1978 from19683To1983) (join_population from19683To1984 from19683To2071))

private theorem fee4At20178 :
    PopulationFees20258.bill (n:=20178) (PopulationFees20258.tabulate (20178-1) 256) PopulationSources20258.source001.plan.table+
      4*20178*NaturalPopulation20258.weights PopulationSources20258.source001.extras≤PopulationSources20258.source001.plan.scale*75469506612 := by decide +kernel
private theorem from19895To1978 : Segment 46 19895 20178 0 1978 :=
  paid (pc:=79) (v:=75469506612) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At20178 (by decide +kernel)

private theorem from19895To1983 : Segment 46 19895 20178 1978 1983 :=
  paid (pc:=80) (v:=75469506612) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At20178 (by decide +kernel)

private theorem from19895To1984 : Segment 46 19895 20178 1983 1984 :=
  paid (pc:=80) (v:=75469506612) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At20178 (by decide +kernel)

private theorem fee5At20178 :
    PopulationFees20258.bill (n:=20178) (PopulationFees20258.tabulate (20178-1) 256) PopulationSources20258.source002.plan.table+
      4*20178*NaturalPopulation20258.weights PopulationSources20258.source002.extras≤PopulationSources20258.source002.plan.scale*134818923847 := by decide +kernel
private theorem from19895To2071 : Segment 46 19895 20178 1984 2071 :=
  paid (pc:=77) (v:=134818923847) (by decide) PopulationSources20258.source002_valid (by decide +kernel) fee5At20178 (by decide +kernel)

private theorem range19895 : Win 46 19895 20178 :=
  complete (by decide) (by decide) (join_population (join_population from19895To1978 from19895To1983) (join_population from19895To1984 from19895To2071))

private theorem fee4At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source001.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source001.extras≤PopulationSources20258.source001.plan.scale*76051993964 := by decide +kernel
private theorem from20179To2056 : Segment 46 20179 20257 0 2056 :=
  paid (pc:=80) (v:=76051993964) (by decide) PopulationSources20258.source001_valid (by decide +kernel) fee4At20257 (by decide +kernel)

private theorem fee3At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) JSP233.Credit19227.p3.plan.table+
      4*20257*NaturalPopulation20258.weights JSP233.Credit19227.p3.extras≤JSP233.Credit19227.p3.plan.scale*139737030072 := by decide +kernel
private theorem from20179To2071 : Segment 46 20179 20257 2056 2071 :=
  paid (pc:=73) (v:=139737030072) (by decide) JSP233.Credit19227.p3_valid (by decide +kernel) fee3At20257 (by decide +kernel)

private theorem range20179 : Win 46 20179 20257 :=
  complete (by decide) (by decide) (join_population from20179To2056 from20179To2071)

theorem bridge46 : Win 46 19683 20257 :=
  (join_ground range19683 (join_ground range19895 range20179))

end JSP233.Credit19227
