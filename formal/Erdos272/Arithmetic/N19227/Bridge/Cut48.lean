module

public import Erdos272.Arithmetic.N19227.Sources.P95
public import Erdos272.Arithmetic.N20258.Sources.Source007
public import Erdos272.Arithmetic.N20258.Sources.Source008
public import Erdos272.Arithmetic.N20258.Sources.Source009
public import Erdos272.Arithmetic.N20258.Sources.Source010
public import Erdos272.Arithmetic.N20258.Sources.Source011
public import Erdos272.Arithmetic.N20258.Sources.Source012
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee9At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source007.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source007.extras≤PopulationSources20258.source007.plan.scale*62379771638 := by decide +kernel
private theorem from19683To2028 : Segment 48 19683 19872 0 2028 :=
  paid (pc:=79) (v:=62379771638) (by decide) PopulationSources20258.source007_valid (by decide +kernel) fee9At19872 (by decide +kernel)

private theorem fee10At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source008.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source008.extras≤PopulationSources20258.source008.plan.scale*124441161625 := by decide +kernel
private theorem from19683To2121 : Segment 48 19683 19872 2028 2121 :=
  paid (pc:=79) (v:=124441161625) (by decide) PopulationSources20258.source008_valid (by decide +kernel) fee10At19872 (by decide +kernel)

private theorem fee11At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source009.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source009.extras≤PopulationSources20258.source009.plan.scale*157672117736 := by decide +kernel
private theorem from19683To2170 : Segment 48 19683 19872 2121 2170 :=
  paid (pc:=78) (v:=157672117736) (by decide) PopulationSources20258.source009_valid (by decide +kernel) fee11At19872 (by decide +kernel)

private theorem fee12At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source010.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source010.extras≤PopulationSources20258.source010.plan.scale*151215363525 := by decide +kernel
private theorem from19683To2209 : Segment 48 19683 19872 2170 2209 :=
  paid (pc:=78) (v:=151215363525) (by decide) PopulationSources20258.source010_valid (by decide +kernel) fee12At19872 (by decide +kernel)

private theorem fee13At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source011.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source011.extras≤PopulationSources20258.source011.plan.scale*146054691030 := by decide +kernel
private theorem from19683To2240 : Segment 48 19683 19872 2209 2240 :=
  paid (pc:=78) (v:=146054691030) (by decide) PopulationSources20258.source011_valid (by decide +kernel) fee13At19872 (by decide +kernel)

private theorem from19683To2241 : Segment 48 19683 19872 2240 2241 :=
  paid (pc:=78) (v:=146054691030) (by decide) PopulationSources20258.source011_valid (by decide +kernel) fee13At19872 (by decide +kernel)

private theorem fee14At19872 :
    PopulationFees20258.bill (n:=19872) (PopulationFees20258.tabulate (19872-1) 256) PopulationSources20258.source012.plan.table+
      4*19872*NaturalPopulation20258.weights PopulationSources20258.source012.extras≤PopulationSources20258.source012.plan.scale*142069707855 := by decide +kernel
private theorem from19683To2257 : Segment 48 19683 19872 2241 2257 :=
  paid (pc:=76) (v:=142069707855) (by decide) PopulationSources20258.source012_valid (by decide +kernel) fee14At19872 (by decide +kernel)

private theorem range19683 : Win 48 19683 19872 :=
  complete (by decide) (by decide) (join_population (join_population from19683To2028 (join_population from19683To2121 from19683To2170)) (join_population (join_population from19683To2209 from19683To2240) (join_population from19683To2241 from19683To2257)))

private theorem fee9At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source007.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source007.extras≤PopulationSources20258.source007.plan.scale*63733053306 := by decide +kernel
private theorem from19873To2036 : Segment 48 19873 20100 0 2036 :=
  paid (pc:=80) (v:=63733053306) (by decide) PopulationSources20258.source007_valid (by decide +kernel) fee9At20100 (by decide +kernel)

private theorem fee10At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source008.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source008.extras≤PopulationSources20258.source008.plan.scale*127099913947 := by decide +kernel
private theorem from19873To2125 : Segment 48 19873 20100 2036 2125 :=
  paid (pc:=79) (v:=127099913947) (by decide) PopulationSources20258.source008_valid (by decide +kernel) fee10At20100 (by decide +kernel)

private theorem fee11At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source009.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source009.extras≤PopulationSources20258.source009.plan.scale*161020679922 := by decide +kernel
private theorem from19873To2171 : Segment 48 19873 20100 2125 2171 :=
  paid (pc:=78) (v:=161020679922) (by decide) PopulationSources20258.source009_valid (by decide +kernel) fee11At20100 (by decide +kernel)

private theorem fee12At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source010.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source010.extras≤PopulationSources20258.source010.plan.scale*154445428258 := by decide +kernel
private theorem from19873To2210 : Segment 48 19873 20100 2171 2210 :=
  paid (pc:=78) (v:=154445428258) (by decide) PopulationSources20258.source010_valid (by decide +kernel) fee12At20100 (by decide +kernel)

private theorem fee13At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source011.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source011.extras≤PopulationSources20258.source011.plan.scale*149171190811 := by decide +kernel
private theorem from19873To2241 : Segment 48 19873 20100 2210 2241 :=
  paid (pc:=78) (v:=149171190811) (by decide) PopulationSources20258.source011_valid (by decide +kernel) fee13At20100 (by decide +kernel)

private theorem fee14At20100 :
    PopulationFees20258.bill (n:=20100) (PopulationFees20258.tabulate (20100-1) 256) PopulationSources20258.source012.plan.table+
      4*20100*NaturalPopulation20258.weights PopulationSources20258.source012.extras≤PopulationSources20258.source012.plan.scale*145103401384 := by decide +kernel
private theorem from19873To2257 : Segment 48 19873 20100 2241 2257 :=
  paid (pc:=76) (v:=145103401384) (by decide) PopulationSources20258.source012_valid (by decide +kernel) fee14At20100 (by decide +kernel)

private theorem range19873 : Win 48 19873 20100 :=
  complete (by decide) (by decide) (join_population (join_population from19873To2036 (join_population from19873To2125 from19873To2171)) (join_population from19873To2210 (join_population from19873To2241 from19873To2257)))

private theorem fee9At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source007.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source007.extras≤PopulationSources20258.source007.plan.scale*64735312076 := by decide +kernel
private theorem from20101To2073 : Segment 48 20101 20257 0 2073 :=
  paid (pc:=80) (v:=64735312076) (by decide) PopulationSources20258.source007_valid (by decide +kernel) fee9At20257 (by decide +kernel)

private theorem fee95At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) JSP233.Credit19227.p95.plan.table+
      4*20257*NaturalPopulation20258.weights JSP233.Credit19227.p95.extras≤JSP233.Credit19227.p95.plan.scale*171142466371 := by decide +kernel
private theorem from20101To2171 : Segment 48 20101 20257 2073 2171 :=
  paid (pc:=79) (v:=171142466371) (by decide) JSP233.Credit19227.p95_valid (by decide +kernel) fee95At20257 (by decide +kernel)

private theorem fee12At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source010.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source010.extras≤PopulationSources20258.source010.plan.scale*156778335167 := by decide +kernel
private theorem from20101To2252 : Segment 48 20101 20257 2171 2252 :=
  paid (pc:=78) (v:=156778335167) (by decide) PopulationSources20258.source010_valid (by decide +kernel) fee12At20257 (by decide +kernel)

private theorem fee13At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source011.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source011.extras≤PopulationSources20258.source011.plan.scale*151441121120 := by decide +kernel
private theorem from20101To2257 : Segment 48 20101 20257 2252 2257 :=
  paid (pc:=74) (v:=151441121120) (by decide) PopulationSources20258.source011_valid (by decide +kernel) fee13At20257 (by decide +kernel)

private theorem range20101 : Win 48 20101 20257 :=
  complete (by decide) (by decide) (join_population (join_population from20101To2073 from20101To2171) (join_population from20101To2252 from20101To2257))

theorem bridge48 : Win 48 19683 20257 :=
  (join_ground range19683 (join_ground range19873 range20101))

end JSP233.Credit19227
