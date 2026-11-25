module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source124
public import Erdos272.Arithmetic.N20258.Sources.Source125

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem range74From20258Price : ( .marked ⟨74,216,29,14000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range74From20258 : Win 74 20258 24992 :=
  classical_route (pc:=0) range74From20258Price (by decide +kernel)

private theorem tests74_125_0 : ∀ z∈source125.plan.table,z.1.Valid 74 0 := by decide +kernel
private theorem fee74_125_30843 :
    PopulationFees20258.bill (n:=30843) (PopulationFees20258.tabulate (30843-1) 256) source125.plan.table+
      4*30843*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*692257076007 := by decide +kernel
private theorem range74From24993To5403 : Segment 74 24993 30843 0 5403 :=
  paid (pc:=61) (v:=692257076007) (by decide) source125_valid tests74_125_0 fee74_125_30843 (by decide +kernel)

private theorem range74From24993 : Win 74 24993 30843 :=
  complete (by decide) (by decide) range74From24993To5403

private theorem fee74_125_35804 :
    PopulationFees20258.bill (n:=35804) (PopulationFees20258.tabulate (35804-1) 256) source125.plan.table+
      4*35804*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*905076372783 := by decide +kernel
private theorem range74From30844To4265 : Segment 74 30844 35804 0 4265 :=
  paid (pc:=58) (v:=905076372783) (by decide) source125_valid tests74_125_0 fee74_125_35804 (by decide +kernel)

private theorem tests74_125_4265 : ∀ z∈source125.plan.table,z.1.Valid 74 4265 := by decide +kernel
private theorem range74From30844To4469 : Segment 74 30844 35804 4265 4469 :=
  paid (pc:=56) (v:=905076372783) (by decide) source125_valid tests74_125_4265 fee74_125_35804 (by decide +kernel)

private theorem tests74_125_4469 : ∀ z∈source125.plan.table,z.1.Valid 74 4469 := by decide +kernel
private theorem range74From30844To4508 : Segment 74 30844 35804 4469 4508 :=
  paid (pc:=56) (v:=905076372783) (by decide) source125_valid tests74_125_4469 fee74_125_35804 (by decide +kernel)

private theorem tests74_124_4508 : ∀ z∈source124.plan.table,z.1.Valid 74 4508 := by decide +kernel
private theorem fee74_124_35804 :
    PopulationFees20258.bill (n:=35804) (PopulationFees20258.tabulate (35804-1) 256) source124.plan.table+
      4*35804*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*876645790738 := by decide +kernel
private theorem range74From30844To5403 : Segment 74 30844 35804 4508 5403 :=
  paid (pc:=53) (v:=876645790738) (by decide) source124_valid tests74_124_4508 fee74_124_35804 (by decide +kernel)

private theorem range74From30844 : Win 74 30844 35804 :=
  complete (by decide) (by decide) (join_population (join_population range74From30844To4265 range74From30844To4469) (join_population range74From30844To4508 range74From30844To5403))

private theorem fee74_125_39135 :
    PopulationFees20258.bill (n:=39135) (PopulationFees20258.tabulate (39135-1) 256) source125.plan.table+
      4*39135*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*1063660566175 := by decide +kernel
private theorem range74From35805To5162 : Segment 74 35805 39135 0 5162 :=
  paid (pc:=63) (v:=1063660566175) (by decide) source125_valid tests74_125_0 fee74_125_39135 (by decide +kernel)

private theorem tests74_124_5162 : ∀ z∈source124.plan.table,z.1.Valid 74 5162 := by decide +kernel
private theorem fee74_124_39135 :
    PopulationFees20258.bill (n:=39135) (PopulationFees20258.tabulate (39135-1) 256) source124.plan.table+
      4*39135*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*1031444508656 := by decide +kernel
private theorem range74From35805To5393 : Segment 74 35805 39135 5162 5393 :=
  paid (pc:=62) (v:=1031444508656) (by decide) source124_valid tests74_124_5162 fee74_124_39135 (by decide +kernel)

private theorem tests74_124_5393 : ∀ z∈source124.plan.table,z.1.Valid 74 5393 := by decide +kernel
private theorem range74From35805To5403 : Segment 74 35805 39135 5393 5403 :=
  paid (pc:=62) (v:=1031444508656) (by decide) source124_valid tests74_124_5393 fee74_124_39135 (by decide +kernel)

private theorem range74From35805 : Win 74 35805 39135 :=
  complete (by decide) (by decide) (join_population range74From35805To5162 (join_population range74From35805To5393 range74From35805To5403))

private theorem fee74_125_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source125.plan.table+
      4*39999*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*1106668601675 := by decide +kernel
private theorem range74From39136To5403 : Segment 74 39136 39999 0 5403 :=
  paid (pc:=70) (v:=1106668601675) (by decide) source125_valid tests74_125_0 fee74_125_39999 (by decide +kernel)

private theorem range74From39136 : Win 74 39136 39999 :=
  complete (by decide) (by decide) range74From39136To5403

theorem cut74From20258 : Win 74 20258 39999 :=
  (join_ground (join_ground range74From20258 range74From24993) (join_ground range74From30844 (join_ground range74From35805 range74From39136)))

end JSP233.FiniteCutRanges20258
