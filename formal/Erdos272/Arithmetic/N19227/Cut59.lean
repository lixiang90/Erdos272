module

public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source101
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee81At19525 :
    PopulationFees20258.bill (n:=19525) (PopulationFees20258.tabulate (19525-1) 256) PopulationSources20258.source101.plan.table+
      4*19525*NaturalPopulation20258.weights PopulationSources20258.source101.extras≤PopulationSources20258.source101.plan.scale*151121151039 := by decide +kernel
private theorem from19227To2785 : Segment 59 19227 19525 0 2785 :=
  paid (pc:=72) (v:=151121151039) (by decide) PopulationSources20258.source101_valid (by decide +kernel) fee81At19525 (by decide +kernel)

private theorem fee77At19525 :
    PopulationFees20258.bill (n:=19525) (PopulationFees20258.tabulate (19525-1) 256) PopulationSources20258.source094.plan.table+
      4*19525*NaturalPopulation20258.weights PopulationSources20258.source094.extras≤PopulationSources20258.source094.plan.scale*202507290216 := by decide +kernel
private theorem from19227To2855 : Segment 59 19227 19525 2785 2855 :=
  paid (pc:=71) (v:=202507290216) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At19525 (by decide +kernel)

private theorem from19227To2858 : Segment 59 19227 19525 2855 2858 :=
  paid (pc:=71) (v:=202507290216) (by decide) PopulationSources20258.source094_valid (by decide +kernel) fee77At19525 (by decide +kernel)

private theorem fee80At19525 :
    PopulationFees20258.bill (n:=19525) (PopulationFees20258.tabulate (19525-1) 256) PopulationSources20258.source100.plan.table+
      4*19525*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*225262088215 := by decide +kernel
private theorem from19227To3423 : Segment 59 19227 19525 2858 3423 :=
  paid (pc:=65) (v:=225262088215) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At19525 (by decide +kernel)

private theorem range19227 : Win 59 19227 19525 :=
  complete (by decide) (by decide) (join_population (join_population from19227To2785 from19227To2855) (join_population from19227To2858 from19227To3423))

private theorem fee81At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source101.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source101.extras≤PopulationSources20258.source101.plan.scale*153382181104 := by decide +kernel
private theorem from19526To2863 : Segment 59 19526 19682 0 2863 :=
  paid (pc:=72) (v:=153382181104) (by decide) PopulationSources20258.source101_valid (by decide +kernel) fee81At19682 (by decide +kernel)

private theorem fee80At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source100.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*228638279791 := by decide +kernel
private theorem from19526To3423 : Segment 59 19526 19682 2863 3423 :=
  paid (pc:=66) (v:=228638279791) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At19682 (by decide +kernel)

private theorem range19526 : Win 59 19526 19682 :=
  complete (by decide) (by decide) (join_population from19526To2863 from19526To3423)

theorem cut59 : Win 59 19227 19682 :=
  (join_ground range19227 range19526)

end JSP233.Credit19227
