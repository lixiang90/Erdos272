module

public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source097
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee79At19592 :
    PopulationFees20258.bill (n:=19592) (PopulationFees20258.tabulate (19592-1) 256) PopulationSources20258.source098.plan.table+
      4*19592*NaturalPopulation20258.weights PopulationSources20258.source098.extras≤PopulationSources20258.source098.plan.scale*163102179329 := by decide +kernel
private theorem from19227To2640 : Segment 58 19227 19592 0 2640 :=
  paid (pc:=73) (v:=163102179329) (by decide) PopulationSources20258.source098_valid (by decide +kernel) fee79At19592 (by decide +kernel)

private theorem from19227To2671 : Segment 58 19227 19592 2640 2671 :=
  paid (pc:=72) (v:=163102179329) (by decide) PopulationSources20258.source098_valid (by decide +kernel) fee79At19592 (by decide +kernel)

private theorem fee76At19592 :
    PopulationFees20258.bill (n:=19592) (PopulationFees20258.tabulate (19592-1) 256) PopulationSources20258.source095.plan.table+
      4*19592*NaturalPopulation20258.weights PopulationSources20258.source095.extras≤PopulationSources20258.source095.plan.scale*209829197264 := by decide +kernel
private theorem from19227To2727 : Segment 58 19227 19592 2671 2727 :=
  paid (pc:=72) (v:=209829197264) (by decide) PopulationSources20258.source095_valid (by decide +kernel) fee76At19592 (by decide +kernel)

private theorem fee77At19592 :
    PopulationFees20258.bill (n:=19592) (PopulationFees20258.tabulate (19592-1) 256) PopulationSources20258.source094.plan.table+
      4*19592*NaturalPopulation20258.weights PopulationSources20258.source094.extras≤PopulationSources20258.source094.plan.scale*203712460493 := by decide +kernel
private theorem from19227To2807 : Segment 58 19227 19592 2727 2807 :=
  paid (pc:=71) (v:=203712460493) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At19592 (by decide +kernel)

private theorem from19227To2812 : Segment 58 19227 19592 2807 2812 :=
  paid (pc:=71) (v:=203712460493) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At19592 (by decide +kernel)

private theorem fee80At19592 :
    PopulationFees20258.bill (n:=19592) (PopulationFees20258.tabulate (19592-1) 256) PopulationSources20258.source100.plan.table+
      4*19592*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*226711606699 := by decide +kernel
private theorem from19227To3307 : Segment 58 19227 19592 2812 3307 :=
  paid (pc:=66) (v:=226711606699) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At19592 (by decide +kernel)

private theorem range19227 : Win 58 19227 19592 :=
  complete (by decide) (by decide) (join_population (join_population from19227To2640 (join_population from19227To2671 from19227To2727)) (join_population from19227To2807 (join_population from19227To2812 from19227To3307)))

private theorem fee79At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source098.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source098.extras≤PopulationSources20258.source098.plan.scale*164513552873 := by decide +kernel
private theorem from19593To2797 : Segment 58 19593 19682 0 2797 :=
  paid (pc:=73) (v:=164513552873) (by decide) PopulationSources20258.source098_valid (by decide +kernel) fee79At19682 (by decide +kernel)

private theorem fee77At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source094.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source094.extras≤PopulationSources20258.source094.plan.scale*205387731181 := by decide +kernel
private theorem from19593To2996 : Segment 58 19593 19682 2797 2996 :=
  paid (pc:=71) (v:=205387731181) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At19682 (by decide +kernel)

private theorem fee78At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source097.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source097.extras≤PopulationSources20258.source097.plan.scale*215164747163 := by decide +kernel
private theorem from19593To3307 : Segment 58 19593 19682 2996 3307 :=
  paid (pc:=67) (v:=215164747163) (by decide) PopulationSources20258.source097_valid (by decide +kernel) fee78At19682 (by decide +kernel)

private theorem range19593 : Win 58 19593 19682 :=
  complete (by decide) (by decide) (join_population from19593To2797 (join_population from19593To2996 from19593To3307))

theorem cut58 : Win 58 19227 19682 :=
  (join_ground range19227 range19593)

end JSP233.Credit19227
