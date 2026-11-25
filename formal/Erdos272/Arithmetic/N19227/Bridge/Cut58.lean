module

public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee79At20032 :
    PopulationFees20258.bill (n:=20032) (PopulationFees20258.tabulate (20032-1) 256) PopulationSources20258.source098.plan.table+
      4*20032*NaturalPopulation20258.weights PopulationSources20258.source098.extras≤PopulationSources20258.source098.plan.scale*169794187654 := by decide +kernel
private theorem from19683To2661 : Segment 58 19683 20032 0 2661 :=
  paid (pc:=73) (v:=169794187654) (by decide) PopulationSources20258.source098_valid (by decide +kernel) fee79At20032 (by decide +kernel)

private theorem fee76At20032 :
    PopulationFees20258.bill (n:=20032) (PopulationFees20258.tabulate (20032-1) 256) PopulationSources20258.source095.plan.table+
      4*20032*NaturalPopulation20258.weights PopulationSources20258.source095.extras≤PopulationSources20258.source095.plan.scale*218358180311 := by decide +kernel
private theorem from19683To2734 : Segment 58 19683 20032 2661 2734 :=
  paid (pc:=72) (v:=218358180311) (by decide) PopulationSources20258.source095_valid (by decide +kernel) fee76At20032 (by decide +kernel)

private theorem fee77At20032 :
    PopulationFees20258.bill (n:=20032) (PopulationFees20258.tabulate (20032-1) 256) PopulationSources20258.source094.plan.table+
      4*20032*NaturalPopulation20258.weights PopulationSources20258.source094.extras≤PopulationSources20258.source094.plan.scale*211999081789 := by decide +kernel
private theorem from19683To2807 : Segment 58 19683 20032 2734 2807 :=
  paid (pc:=72) (v:=211999081789) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At20032 (by decide +kernel)

private theorem from19683To2812 : Segment 58 19683 20032 2807 2812 :=
  paid (pc:=72) (v:=211999081789) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At20032 (by decide +kernel)

private theorem fee80At20032 :
    PopulationFees20258.bill (n:=20032) (PopulationFees20258.tabulate (20032-1) 256) PopulationSources20258.source100.plan.table+
      4*20032*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*235897310151 := by decide +kernel
private theorem from19683To3307 : Segment 58 19683 20032 2812 3307 :=
  paid (pc:=64) (v:=235897310151) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At20032 (by decide +kernel)

private theorem range19683 : Win 58 19683 20032 :=
  complete (by decide) (by decide) (join_population (join_population from19683To2661 from19683To2734) (join_population from19683To2807 (join_population from19683To2812 from19683To3307)))

private theorem fee79At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source098.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source098.extras≤PopulationSources20258.source098.plan.scale*173301378994 := by decide +kernel
private theorem from20033To2734 : Segment 58 20033 20257 0 2734 :=
  paid (pc:=74) (v:=173301378994) (by decide) PopulationSources20258.source098_valid (by decide +kernel) fee79At20257 (by decide +kernel)

private theorem fee77At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source094.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source094.extras≤PopulationSources20258.source094.plan.scale*216412275936 := by decide +kernel
private theorem from20033To2884 : Segment 58 20033 20257 2734 2884 :=
  paid (pc:=72) (v:=216412275936) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At20257 (by decide +kernel)

private theorem fee80At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source100.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*240730291020 := by decide +kernel
private theorem from20033To3307 : Segment 58 20033 20257 2884 3307 :=
  paid (pc:=63) (v:=240730291020) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At20257 (by decide +kernel)

private theorem range20033 : Win 58 20033 20257 :=
  complete (by decide) (by decide) (join_population from20033To2734 (join_population from20033To2884 from20033To3307))

theorem bridge58 : Win 58 19683 20257 :=
  (join_ground range19683 range20033)

end JSP233.Credit19227
