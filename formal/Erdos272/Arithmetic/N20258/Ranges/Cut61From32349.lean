module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source109

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests61_107_0 : ∀ z∈source107.plan.table,z.1.Valid 61 0 := by decide +kernel
private theorem fee61_107_34097 :
    PopulationFees20258.bill (n:=34097) (PopulationFees20258.tabulate (34097-1) 256) source107.plan.table+
      4*34097*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*462273466699 := by decide +kernel
private theorem range61From32349To3302 : Segment 61 32349 34097 0 3302 :=
  paid (pc:=75) (v:=462273466699) (by decide) source107_valid tests61_107_0 fee61_107_34097 (by decide +kernel)

private theorem tests61_105_3302 : ∀ z∈source105.plan.table,z.1.Valid 61 3302 := by decide +kernel
private theorem fee61_105_34097 :
    PopulationFees20258.bill (n:=34097) (PopulationFees20258.tabulate (34097-1) 256) source105.plan.table+
      4*34097*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*634662864993 := by decide +kernel
private theorem range61From32349To3417 : Segment 61 32349 34097 3302 3417 :=
  paid (pc:=75) (v:=634662864993) (by decide) source105_valid tests61_105_3302 fee61_105_34097 (by decide +kernel)

private theorem tests61_105_3417 : ∀ z∈source105.plan.table,z.1.Valid 61 3417 := by decide +kernel
private theorem range61From32349To3419 : Segment 61 32349 34097 3417 3419 :=
  paid (pc:=75) (v:=634662864993) (by decide) source105_valid tests61_105_3417 fee61_105_34097 (by decide +kernel)

private theorem tests61_108_3419 : ∀ z∈source108.plan.table,z.1.Valid 61 3419 := by decide +kernel
private theorem fee61_108_34097 :
    PopulationFees20258.bill (n:=34097) (PopulationFees20258.tabulate (34097-1) 256) source108.plan.table+
      4*34097*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*525707302290 := by decide +kernel
private theorem range61From32349To3661 : Segment 61 32349 34097 3419 3661 :=
  paid (pc:=73) (v:=525707302290) (by decide) source108_valid tests61_108_3419 fee61_108_34097 (by decide +kernel)

private theorem range61From32349 : Win 61 32349 34097 :=
  complete (by decide) (by decide) (join_population (join_population range61From32349To3302 range61From32349To3417) (join_population range61From32349To3419 range61From32349To3661))

private theorem fee61_107_36264 :
    PopulationFees20258.bill (n:=36264) (PopulationFees20258.tabulate (36264-1) 256) source107.plan.table+
      4*36264*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*518917456810 := by decide +kernel
private theorem range61From34098To3332 : Segment 61 34098 36264 0 3332 :=
  paid (pc:=75) (v:=518917456810) (by decide) source107_valid tests61_107_0 fee61_107_36264 (by decide +kernel)

private theorem tests61_105_3332 : ∀ z∈source105.plan.table,z.1.Valid 61 3332 := by decide +kernel
private theorem fee61_105_36264 :
    PopulationFees20258.bill (n:=36264) (PopulationFees20258.tabulate (36264-1) 256) source105.plan.table+
      4*36264*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*712211779995 := by decide +kernel
private theorem range61From34098To3418 : Segment 61 34098 36264 3332 3418 :=
  paid (pc:=74) (v:=712211779995) (by decide) source105_valid tests61_105_3332 fee61_105_36264 (by decide +kernel)

private theorem tests61_105_3418 : ∀ z∈source105.plan.table,z.1.Valid 61 3418 := by decide +kernel
private theorem range61From34098To3419 : Segment 61 34098 36264 3418 3419 :=
  paid (pc:=74) (v:=712211779995) (by decide) source105_valid tests61_105_3418 fee61_105_36264 (by decide +kernel)

private theorem fee61_108_36264 :
    PopulationFees20258.bill (n:=36264) (PopulationFees20258.tabulate (36264-1) 256) source108.plan.table+
      4*36264*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*590221385434 := by decide +kernel
private theorem range61From34098To3646 : Segment 61 34098 36264 3419 3646 :=
  paid (pc:=73) (v:=590221385434) (by decide) source108_valid tests61_108_3419 fee61_108_36264 (by decide +kernel)

private theorem tests61_109_3646 : ∀ z∈source109.plan.table,z.1.Valid 61 3646 := by decide +kernel
private theorem fee61_109_36264 :
    PopulationFees20258.bill (n:=36264) (PopulationFees20258.tabulate (36264-1) 256) source109.plan.table+
      4*36264*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*584585776009 := by decide +kernel
private theorem range61From34098To3661 : Segment 61 34098 36264 3646 3661 :=
  paid (pc:=73) (v:=584585776009) (by decide) source109_valid tests61_109_3646 fee61_109_36264 (by decide +kernel)

private theorem range61From34098 : Win 61 34098 36264 :=
  complete (by decide) (by decide) (join_population (join_population range61From34098To3332 range61From34098To3418) (join_population range61From34098To3419 (join_population range61From34098To3646 range61From34098To3661)))

private theorem fee61_107_38976 :
    PopulationFees20258.bill (n:=38976) (PopulationFees20258.tabulate (38976-1) 256) source107.plan.table+
      4*38976*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*594376673547 := by decide +kernel
private theorem range61From36265To3374 : Segment 61 36265 38976 0 3374 :=
  paid (pc:=75) (v:=594376673547) (by decide) source107_valid tests61_107_0 fee61_107_38976 (by decide +kernel)

private theorem tests61_105_3374 : ∀ z∈source105.plan.table,z.1.Valid 61 3374 := by decide +kernel
private theorem fee61_105_38976 :
    PopulationFees20258.bill (n:=38976) (PopulationFees20258.tabulate (38976-1) 256) source105.plan.table+
      4*38976*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*814556911754 := by decide +kernel
private theorem range61From36265To3435 : Segment 61 36265 38976 3374 3435 :=
  paid (pc:=74) (v:=814556911754) (by decide) source105_valid tests61_105_3374 fee61_105_38976 (by decide +kernel)

private theorem tests61_108_3435 : ∀ z∈source108.plan.table,z.1.Valid 61 3435 := by decide +kernel
private theorem fee61_108_38976 :
    PopulationFees20258.bill (n:=38976) (PopulationFees20258.tabulate (38976-1) 256) source108.plan.table+
      4*38976*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*676172364282 := by decide +kernel
private theorem range61From36265To3648 : Segment 61 36265 38976 3435 3648 :=
  paid (pc:=73) (v:=676172364282) (by decide) source108_valid tests61_108_3435 fee61_108_38976 (by decide +kernel)

private theorem tests61_109_3648 : ∀ z∈source109.plan.table,z.1.Valid 61 3648 := by decide +kernel
private theorem fee61_109_38976 :
    PopulationFees20258.bill (n:=38976) (PopulationFees20258.tabulate (38976-1) 256) source109.plan.table+
      4*38976*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*669773969309 := by decide +kernel
private theorem range61From36265To3661 : Segment 61 36265 38976 3648 3661 :=
  paid (pc:=73) (v:=669773969309) (by decide) source109_valid tests61_109_3648 fee61_109_38976 (by decide +kernel)

private theorem range61From36265 : Win 61 36265 38976 :=
  complete (by decide) (by decide) (join_population (join_population range61From36265To3374 range61From36265To3435) (join_population range61From36265To3648 range61From36265To3661))

private theorem range61From38977Price : ( .marked ⟨61,163,24,8000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range61From38977 : Win 61 38977 39999 :=
  classical_route (pc:=80) range61From38977Price (by decide +kernel)

theorem cut61From32349 : Win 61 32349 39999 :=
  (join_ground (join_ground range61From32349 range61From34098) (join_ground range61From36265 range61From38977))

end JSP233.FiniteCutRanges20258
