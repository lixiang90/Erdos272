module

public import Erdos272.Arithmetic.N19227.Sources.P93
public import Erdos272.Arithmetic.N20258.Sources.Source003
public import Erdos272.Arithmetic.N20258.Sources.Source004
public import Erdos272.Arithmetic.N20258.Sources.Source005
public import Erdos272.Arithmetic.N20258.Sources.Source006
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee6At19888 :
    PopulationFees20258.bill (n:=19888) (PopulationFees20258.tabulate (19888-1) 256) PopulationSources20258.source003.plan.table+
      4*19888*NaturalPopulation20258.weights PopulationSources20258.source003.extras≤PopulationSources20258.source003.plan.scale*68190722442 := by decide +kernel
private theorem from19683To2001 : Segment 47 19683 19888 0 2001 :=
  paid (pc:=80) (v:=68190722442) (by decide) PopulationSources20258.source003_valid (by decide +kernel) fee6At19888 (by decide +kernel)

private theorem from19683To2006 : Segment 47 19683 19888 2001 2006 :=
  paid (pc:=79) (v:=68190722442) (by decide) PopulationSources20258.source003_valid (by decide +kernel) fee6At19888 (by decide +kernel)

private theorem fee7At19888 :
    PopulationFees20258.bill (n:=19888) (PopulationFees20258.tabulate (19888-1) 256) PopulationSources20258.source004.plan.table+
      4*19888*NaturalPopulation20258.weights PopulationSources20258.source004.extras≤PopulationSources20258.source004.plan.scale*127594866644 := by decide +kernel
private theorem from19683To2101 : Segment 47 19683 19888 2006 2101 :=
  paid (pc:=79) (v:=127594866644) (by decide) PopulationSources20258.source004_valid (by decide +kernel) fee7At19888 (by decide +kernel)

private theorem from19683To2104 : Segment 47 19683 19888 2101 2104 :=
  paid (pc:=79) (v:=127594866644) (by decide) PopulationSources20258.source004_valid (by decide +kernel) fee7At19888 (by decide +kernel)

private theorem fee93At19888 :
    PopulationFees20258.bill (n:=19888) (PopulationFees20258.tabulate (19888-1) 256) JSP233.Credit19227.p93.plan.table+
      4*19888*NaturalPopulation20258.weights JSP233.Credit19227.p93.extras≤JSP233.Credit19227.p93.plan.scale*159970609352 := by decide +kernel
private theorem from19683To2153 : Segment 47 19683 19888 2104 2153 :=
  paid (pc:=79) (v:=159970609352) (by decide) JSP233.Credit19227.p93_valid (by decide +kernel) fee93At19888 (by decide +kernel)

private theorem fee94At19888 :
    PopulationFees20258.bill (n:=19888) (PopulationFees20258.tabulate (19888-1) 256) PopulationSources20258.source006.plan.table+
      4*19888*NaturalPopulation20258.weights PopulationSources20258.source006.extras≤PopulationSources20258.source006.plan.scale*152790508483 := by decide +kernel
private theorem from19683To2163 : Segment 47 19683 19888 2153 2163 :=
  paid (pc:=74) (v:=152790508483) (by decide) PopulationSources20258.source006_valid (by decide +kernel) fee94At19888 (by decide +kernel)

private theorem range19683 : Win 47 19683 19888 :=
  complete (by decide) (by decide) (join_population (join_population from19683To2001 (join_population from19683To2006 from19683To2101)) (join_population from19683To2104 (join_population from19683To2153 from19683To2163)))

private theorem fee6At20147 :
    PopulationFees20258.bill (n:=20147) (PopulationFees20258.tabulate (20147-1) 256) PopulationSources20258.source003.plan.table+
      4*20147*NaturalPopulation20258.weights PopulationSources20258.source003.extras≤PopulationSources20258.source003.plan.scale*69883864810 := by decide +kernel
private theorem from19889To2005 : Segment 47 19889 20147 0 2005 :=
  paid (pc:=80) (v:=69883864810) (by decide) PopulationSources20258.source003_valid (by decide +kernel) fee6At20147 (by decide +kernel)

private theorem fee7At20147 :
    PopulationFees20258.bill (n:=20147) (PopulationFees20258.tabulate (20147-1) 256) PopulationSources20258.source004.plan.table+
      4*20147*NaturalPopulation20258.weights PopulationSources20258.source004.extras≤PopulationSources20258.source004.plan.scale*130701726203 := by decide +kernel
private theorem from19889To2101 : Segment 47 19889 20147 2005 2101 :=
  paid (pc:=79) (v:=130701726203) (by decide) PopulationSources20258.source004_valid (by decide +kernel) fee7At20147 (by decide +kernel)

private theorem from19889To2104 : Segment 47 19889 20147 2101 2104 :=
  paid (pc:=79) (v:=130701726203) (by decide) PopulationSources20258.source004_valid (by decide +kernel) fee7At20147 (by decide +kernel)

private theorem fee93At20147 :
    PopulationFees20258.bill (n:=20147) (PopulationFees20258.tabulate (20147-1) 256) JSP233.Credit19227.p93.plan.table+
      4*20147*NaturalPopulation20258.weights JSP233.Credit19227.p93.extras≤JSP233.Credit19227.p93.plan.scale*163859597147 := by decide +kernel
private theorem from19889To2150 : Segment 47 19889 20147 2104 2150 :=
  paid (pc:=79) (v:=163859597147) (by decide) JSP233.Credit19227.p93_valid (by decide +kernel) fee93At20147 (by decide +kernel)

private theorem fee8At20147 :
    PopulationFees20258.bill (n:=20147) (PopulationFees20258.tabulate (20147-1) 256) PopulationSources20258.source005.plan.table+
      4*20147*NaturalPopulation20258.weights PopulationSources20258.source005.extras≤PopulationSources20258.source005.plan.scale*163194121703 := by decide +kernel
private theorem from19889To2155 : Segment 47 19889 20147 2150 2155 :=
  paid (pc:=79) (v:=163194121703) (by decide) PopulationSources20258.source005_valid (by decide +kernel) fee8At20147 (by decide +kernel)

private theorem fee94At20147 :
    PopulationFees20258.bill (n:=20147) (PopulationFees20258.tabulate (20147-1) 256) PopulationSources20258.source006.plan.table+
      4*20147*NaturalPopulation20258.weights PopulationSources20258.source006.extras≤PopulationSources20258.source006.plan.scale*156515034085 := by decide +kernel
private theorem from19889To2163 : Segment 47 19889 20147 2155 2163 :=
  paid (pc:=74) (v:=156515034085) (by decide) PopulationSources20258.source006_valid (by decide +kernel) fee94At20147 (by decide +kernel)

private theorem range19889 : Win 47 19889 20147 :=
  complete (by decide) (by decide) (join_population (join_population from19889To2005 (join_population from19889To2101 from19889To2104)) (join_population from19889To2150 (join_population from19889To2155 from19889To2163)))

private theorem fee6At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source003.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source003.extras≤PopulationSources20258.source003.plan.scale*70641882884 := by decide +kernel
private theorem from20148To2066 : Segment 47 20148 20257 0 2066 :=
  paid (pc:=80) (v:=70641882884) (by decide) PopulationSources20258.source003_valid (by decide +kernel) fee6At20257 (by decide +kernel)

private theorem fee7At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source004.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source004.extras≤PopulationSources20258.source004.plan.scale*132099652959 := by decide +kernel
private theorem from20148To2163 : Segment 47 20148 20257 2066 2163 :=
  paid (pc:=77) (v:=132099652959) (by decide) PopulationSources20258.source004_valid (by decide +kernel) fee7At20257 (by decide +kernel)

private theorem range20148 : Win 47 20148 20257 :=
  complete (by decide) (by decide) (join_population from20148To2066 from20148To2163)

theorem bridge47 : Win 47 19683 20257 :=
  (join_ground range19683 (join_ground range19889 range20148))

end JSP233.Credit19227
