module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source099
public import Erdos272.Arithmetic.N20258.Sources.Source101
public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source103

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests59_101_0 : ∀ z∈source101.plan.table,z.1.Valid 59 0 := by decide +kernel
private theorem fee59_101_23551 :
    PopulationFees20258.bill (n:=23551) (PopulationFees20258.tabulate (23551-1) 256) source101.plan.table+
      4*23551*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*212746901698 := by decide +kernel
private theorem range59From23185To2905 : Segment 59 23185 23551 0 2905 :=
  paid (pc:=75) (v:=212746901698) (by decide) source101_valid tests59_101_0 fee59_101_23551 (by decide +kernel)

private theorem tests59_099_2905 : ∀ z∈source099.plan.table,z.1.Valid 59 2905 := by decide +kernel
private theorem fee59_099_23551 :
    PopulationFees20258.bill (n:=23551) (PopulationFees20258.tabulate (23551-1) 256) source099.plan.table+
      4*23551*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*307546916774 := by decide +kernel
private theorem range59From23185To3191 : Segment 59 23185 23551 2905 3191 :=
  paid (pc:=73) (v:=307546916774) (by decide) source099_valid tests59_099_2905 fee59_099_23551 (by decide +kernel)

private theorem tests59_096_3191 : ∀ z∈source096.plan.table,z.1.Valid 59 3191 := by decide +kernel
private theorem fee59_096_23551 :
    PopulationFees20258.bill (n:=23551) (PopulationFees20258.tabulate (23551-1) 256) source096.plan.table+
      4*23551*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*276985505935 := by decide +kernel
private theorem range59From23185To3417 : Segment 59 23185 23551 3191 3417 :=
  paid (pc:=71) (v:=276985505935) (by decide) source096_valid tests59_096_3191 fee59_096_23551 (by decide +kernel)

private theorem tests59_096_3417 : ∀ z∈source096.plan.table,z.1.Valid 59 3417 := by decide +kernel
private theorem range59From23185To3423 : Segment 59 23185 23551 3417 3423 :=
  paid (pc:=71) (v:=276985505935) (by decide) source096_valid tests59_096_3417 fee59_096_23551 (by decide +kernel)

private theorem range59From23185 : Win 59 23185 23551 :=
  complete (by decide) (by decide) (join_population (join_population range59From23185To2905 range59From23185To3191) (join_population range59From23185To3417 range59From23185To3423))

private theorem fee59_101_23912 :
    PopulationFees20258.bill (n:=23912) (PopulationFees20258.tabulate (23912-1) 256) source101.plan.table+
      4*23912*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*218641656731 := by decide +kernel
private theorem range59From23552To2929 : Segment 59 23552 23912 0 2929 :=
  paid (pc:=75) (v:=218641656731) (by decide) source101_valid tests59_101_0 fee59_101_23912 (by decide +kernel)

private theorem tests59_103_2929 : ∀ z∈source103.plan.table,z.1.Valid 59 2929 := by decide +kernel
private theorem fee59_103_23912 :
    PopulationFees20258.bill (n:=23912) (PopulationFees20258.tabulate (23912-1) 256) source103.plan.table+
      4*23912*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*302030716391 := by decide +kernel
private theorem range59From23552To3292 : Segment 59 23552 23912 2929 3292 :=
  paid (pc:=73) (v:=302030716391) (by decide) source103_valid tests59_103_2929 fee59_103_23912 (by decide +kernel)

private theorem tests59_096_3292 : ∀ z∈source096.plan.table,z.1.Valid 59 3292 := by decide +kernel
private theorem fee59_096_23912 :
    PopulationFees20258.bill (n:=23912) (PopulationFees20258.tabulate (23912-1) 256) source096.plan.table+
      4*23912*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*284671917474 := by decide +kernel
private theorem range59From23552To3420 : Segment 59 23552 23912 3292 3420 :=
  paid (pc:=72) (v:=284671917474) (by decide) source096_valid tests59_096_3292 fee59_096_23912 (by decide +kernel)

private theorem tests59_096_3420 : ∀ z∈source096.plan.table,z.1.Valid 59 3420 := by decide +kernel
private theorem range59From23552To3423 : Segment 59 23552 23912 3420 3423 :=
  paid (pc:=72) (v:=284671917474) (by decide) source096_valid tests59_096_3420 fee59_096_23912 (by decide +kernel)

private theorem range59From23552 : Win 59 23552 23912 :=
  complete (by decide) (by decide) (join_population (join_population range59From23552To2929 range59From23552To3292) (join_population range59From23552To3420 range59From23552To3423))

private theorem fee59_101_24274 :
    PopulationFees20258.bill (n:=24274) (PopulationFees20258.tabulate (24274-1) 256) source101.plan.table+
      4*24274*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*224705447042 := by decide +kernel
private theorem range59From23913To2952 : Segment 59 23913 24274 0 2952 :=
  paid (pc:=76) (v:=224705447042) (by decide) source101_valid tests59_101_0 fee59_101_24274 (by decide +kernel)

private theorem tests59_102_2952 : ∀ z∈source102.plan.table,z.1.Valid 59 2952 := by decide +kernel
private theorem fee59_102_24274 :
    PopulationFees20258.bill (n:=24274) (PopulationFees20258.tabulate (24274-1) 256) source102.plan.table+
      4*24274*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*303701998174 := by decide +kernel
private theorem range59From23913To3339 : Segment 59 23913 24274 2952 3339 :=
  paid (pc:=73) (v:=303701998174) (by decide) source102_valid tests59_102_2952 fee59_102_24274 (by decide +kernel)

private theorem tests59_096_3339 : ∀ z∈source096.plan.table,z.1.Valid 59 3339 := by decide +kernel
private theorem fee59_096_24274 :
    PopulationFees20258.bill (n:=24274) (PopulationFees20258.tabulate (24274-1) 256) source096.plan.table+
      4*24274*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*292586497801 := by decide +kernel
private theorem range59From23913To3421 : Segment 59 23913 24274 3339 3421 :=
  paid (pc:=72) (v:=292586497801) (by decide) source096_valid tests59_096_3339 fee59_096_24274 (by decide +kernel)

private theorem tests59_096_3421 : ∀ z∈source096.plan.table,z.1.Valid 59 3421 := by decide +kernel
private theorem range59From23913To3423 : Segment 59 23913 24274 3421 3423 :=
  paid (pc:=72) (v:=292586497801) (by decide) source096_valid tests59_096_3421 fee59_096_24274 (by decide +kernel)

private theorem range59From23913 : Win 59 23913 24274 :=
  complete (by decide) (by decide) (join_population (join_population range59From23913To2952 range59From23913To3339) (join_population range59From23913To3421 range59From23913To3423))

private theorem fee59_101_24640 :
    PopulationFees20258.bill (n:=24640) (PopulationFees20258.tabulate (24640-1) 256) source101.plan.table+
      4*24640*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*231081637586 := by decide +kernel
private theorem range59From24275To2974 : Segment 59 24275 24640 0 2974 :=
  paid (pc:=76) (v:=231081637586) (by decide) source101_valid tests59_101_0 fee59_101_24640 (by decide +kernel)

private theorem tests59_102_2974 : ∀ z∈source102.plan.table,z.1.Valid 59 2974 := by decide +kernel
private theorem fee59_102_24640 :
    PopulationFees20258.bill (n:=24640) (PopulationFees20258.tabulate (24640-1) 256) source102.plan.table+
      4*24640*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*312219832350 := by decide +kernel
private theorem range59From24275To3345 : Segment 59 24275 24640 2974 3345 :=
  paid (pc:=73) (v:=312219832350) (by decide) source102_valid tests59_102_2974 fee59_102_24640 (by decide +kernel)

private theorem tests59_096_3345 : ∀ z∈source096.plan.table,z.1.Valid 59 3345 := by decide +kernel
private theorem fee59_096_24640 :
    PopulationFees20258.bill (n:=24640) (PopulationFees20258.tabulate (24640-1) 256) source096.plan.table+
      4*24640*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*300796877405 := by decide +kernel
private theorem range59From24275To3422 : Segment 59 24275 24640 3345 3422 :=
  paid (pc:=72) (v:=300796877405) (by decide) source096_valid tests59_096_3345 fee59_096_24640 (by decide +kernel)

private theorem tests59_096_3422 : ∀ z∈source096.plan.table,z.1.Valid 59 3422 := by decide +kernel
private theorem range59From24275To3423 : Segment 59 24275 24640 3422 3423 :=
  paid (pc:=72) (v:=300796877405) (by decide) source096_valid tests59_096_3422 fee59_096_24640 (by decide +kernel)

private theorem range59From24275 : Win 59 24275 24640 :=
  complete (by decide) (by decide) (join_population (join_population range59From24275To2974 range59From24275To3345) (join_population range59From24275To3422 range59From24275To3423))

private theorem fee59_101_25019 :
    PopulationFees20258.bill (n:=25019) (PopulationFees20258.tabulate (25019-1) 256) source101.plan.table+
      4*25019*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*237608570478 := by decide +kernel
private theorem range59From24641To2994 : Segment 59 24641 25019 0 2994 :=
  paid (pc:=76) (v:=237608570478) (by decide) source101_valid tests59_101_0 fee59_101_25019 (by decide +kernel)

private theorem tests59_102_2994 : ∀ z∈source102.plan.table,z.1.Valid 59 2994 := by decide +kernel
private theorem fee59_102_25019 :
    PopulationFees20258.bill (n:=25019) (PopulationFees20258.tabulate (25019-1) 256) source102.plan.table+
      4*25019*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*320978046481 := by decide +kernel
private theorem range59From24641To3347 : Segment 59 24641 25019 2994 3347 :=
  paid (pc:=73) (v:=320978046481) (by decide) source102_valid tests59_102_2994 fee59_102_25019 (by decide +kernel)

private theorem tests59_096_3347 : ∀ z∈source096.plan.table,z.1.Valid 59 3347 := by decide +kernel
private theorem fee59_096_25019 :
    PopulationFees20258.bill (n:=25019) (PopulationFees20258.tabulate (25019-1) 256) source096.plan.table+
      4*25019*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*309366275687 := by decide +kernel
private theorem range59From24641To3421 : Segment 59 24641 25019 3347 3421 :=
  paid (pc:=73) (v:=309366275687) (by decide) source096_valid tests59_096_3347 fee59_096_25019 (by decide +kernel)

private theorem range59From24641To3423 : Segment 59 24641 25019 3421 3423 :=
  paid (pc:=73) (v:=309366275687) (by decide) source096_valid tests59_096_3421 fee59_096_25019 (by decide +kernel)

private theorem range59From24641 : Win 59 24641 25019 :=
  complete (by decide) (by decide) (join_population (join_population range59From24641To2994 range59From24641To3347) (join_population range59From24641To3421 range59From24641To3423))

private theorem fee59_101_25413 :
    PopulationFees20258.bill (n:=25413) (PopulationFees20258.tabulate (25413-1) 256) source101.plan.table+
      4*25413*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*244541722231 := by decide +kernel
private theorem range59From25020To3013 : Segment 59 25020 25413 0 3013 :=
  paid (pc:=76) (v:=244541722231) (by decide) source101_valid tests59_101_0 fee59_101_25413 (by decide +kernel)

private theorem tests59_102_3013 : ∀ z∈source102.plan.table,z.1.Valid 59 3013 := by decide +kernel
private theorem fee59_102_25413 :
    PopulationFees20258.bill (n:=25413) (PopulationFees20258.tabulate (25413-1) 256) source102.plan.table+
      4*25413*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*330261142150 := by decide +kernel
private theorem range59From25020To3351 : Segment 59 25020 25413 3013 3351 :=
  paid (pc:=74) (v:=330261142150) (by decide) source102_valid tests59_102_3013 fee59_102_25413 (by decide +kernel)

private theorem tests59_096_3351 : ∀ z∈source096.plan.table,z.1.Valid 59 3351 := by decide +kernel
private theorem fee59_096_25413 :
    PopulationFees20258.bill (n:=25413) (PopulationFees20258.tabulate (25413-1) 256) source096.plan.table+
      4*25413*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*318513450155 := by decide +kernel
private theorem range59From25020To3421 : Segment 59 25020 25413 3351 3421 :=
  paid (pc:=73) (v:=318513450155) (by decide) source096_valid tests59_096_3351 fee59_096_25413 (by decide +kernel)

private theorem range59From25020To3423 : Segment 59 25020 25413 3421 3423 :=
  paid (pc:=73) (v:=318513450155) (by decide) source096_valid tests59_096_3421 fee59_096_25413 (by decide +kernel)

private theorem range59From25020 : Win 59 25020 25413 :=
  complete (by decide) (by decide) (join_population (join_population range59From25020To3013 range59From25020To3351) (join_population range59From25020To3421 range59From25020To3423))

theorem cut59From23185 : Win 59 23185 25413 :=
  (join_ground (join_ground range59From23185 (join_ground range59From23552 range59From23913)) (join_ground range59From24275 (join_ground range59From24641 range59From25020)))

end JSP233.FiniteCutRanges20258
