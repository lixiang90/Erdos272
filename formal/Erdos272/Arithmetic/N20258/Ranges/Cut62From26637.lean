module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source110
public import Erdos272.Arithmetic.N20258.Sources.Source112

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests62_110_0 : ∀ z∈source110.plan.table,z.1.Valid 62 0 := by decide +kernel
private theorem fee62_110_27360 :
    PopulationFees20258.bill (n:=27360) (PopulationFees20258.tabulate (27360-1) 256) source110.plan.table+
      4*27360*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*283023049611 := by decide +kernel
private theorem range62From26637To3281 : Segment 62 26637 27360 0 3281 :=
  paid (pc:=74) (v:=283023049611) (by decide) source110_valid tests62_110_0 fee62_110_27360 (by decide +kernel)

private theorem tests62_105_3281 : ∀ z∈source105.plan.table,z.1.Valid 62 3281 := by decide +kernel
private theorem fee62_105_27360 :
    PopulationFees20258.bill (n:=27360) (PopulationFees20258.tabulate (27360-1) 256) source105.plan.table+
      4*27360*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*422725359391 := by decide +kernel
private theorem range62From26637To3469 : Segment 62 26637 27360 3281 3469 :=
  paid (pc:=73) (v:=422725359391) (by decide) source105_valid tests62_105_3281 fee62_105_27360 (by decide +kernel)

private theorem tests62_105_3469 : ∀ z∈source105.plan.table,z.1.Valid 62 3469 := by decide +kernel
private theorem range62From26637To3474 : Segment 62 26637 27360 3469 3474 :=
  paid (pc:=73) (v:=422725359391) (by decide) source105_valid tests62_105_3469 fee62_105_27360 (by decide +kernel)

private theorem tests62_108_3474 : ∀ z∈source108.plan.table,z.1.Valid 62 3474 := by decide +kernel
private theorem fee62_108_27360 :
    PopulationFees20258.bill (n:=27360) (PopulationFees20258.tabulate (27360-1) 256) source108.plan.table+
      4*27360*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*348929168589 := by decide +kernel
private theorem range62From26637To3783 : Segment 62 26637 27360 3474 3783 :=
  paid (pc:=71) (v:=348929168589) (by decide) source108_valid tests62_108_3474 fee62_108_27360 (by decide +kernel)

private theorem range62From26637 : Win 62 26637 27360 :=
  complete (by decide) (by decide) (join_population (join_population range62From26637To3281 range62From26637To3469) (join_population range62From26637To3474 range62From26637To3783))

private theorem fee62_110_28142 :
    PopulationFees20258.bill (n:=28142) (PopulationFees20258.tabulate (28142-1) 256) source110.plan.table+
      4*28142*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*298412698913 := by decide +kernel
private theorem range62From27361To3304 : Segment 62 27361 28142 0 3304 :=
  paid (pc:=75) (v:=298412698913) (by decide) source110_valid tests62_110_0 fee62_110_28142 (by decide +kernel)

private theorem tests62_105_3304 : ∀ z∈source105.plan.table,z.1.Valid 62 3304 := by decide +kernel
private theorem fee62_105_28142 :
    PopulationFees20258.bill (n:=28142) (PopulationFees20258.tabulate (28142-1) 256) source105.plan.table+
      4*28142*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*445309721059 := by decide +kernel
private theorem range62From27361To3470 : Segment 62 27361 28142 3304 3470 :=
  paid (pc:=74) (v:=445309721059) (by decide) source105_valid tests62_105_3304 fee62_105_28142 (by decide +kernel)

private theorem tests62_105_3470 : ∀ z∈source105.plan.table,z.1.Valid 62 3470 := by decide +kernel
private theorem range62From27361To3474 : Segment 62 27361 28142 3470 3474 :=
  paid (pc:=74) (v:=445309721059) (by decide) source105_valid tests62_105_3470 fee62_105_28142 (by decide +kernel)

private theorem fee62_108_28142 :
    PopulationFees20258.bill (n:=28142) (PopulationFees20258.tabulate (28142-1) 256) source108.plan.table+
      4*28142*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*367661558097 := by decide +kernel
private theorem range62From27361To3783 : Segment 62 27361 28142 3474 3783 :=
  paid (pc:=71) (v:=367661558097) (by decide) source108_valid tests62_108_3474 fee62_108_28142 (by decide +kernel)

private theorem range62From27361 : Win 62 27361 28142 :=
  complete (by decide) (by decide) (join_population (join_population range62From27361To3304 range62From27361To3470) (join_population range62From27361To3474 range62From27361To3783))

private theorem fee62_110_29010 :
    PopulationFees20258.bill (n:=29010) (PopulationFees20258.tabulate (29010-1) 256) source110.plan.table+
      4*29010*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*315633617212 := by decide +kernel
private theorem range62From28143To3326 : Segment 62 28143 29010 0 3326 :=
  paid (pc:=75) (v:=315633617212) (by decide) source110_valid tests62_110_0 fee62_110_29010 (by decide +kernel)

private theorem tests62_105_3326 : ∀ z∈source105.plan.table,z.1.Valid 62 3326 := by decide +kernel
private theorem fee62_105_29010 :
    PopulationFees20258.bill (n:=29010) (PopulationFees20258.tabulate (29010-1) 256) source105.plan.table+
      4*29010*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*470971191029 := by decide +kernel
private theorem range62From28143To3471 : Segment 62 28143 29010 3326 3471 :=
  paid (pc:=74) (v:=470971191029) (by decide) source105_valid tests62_105_3326 fee62_105_29010 (by decide +kernel)

private theorem tests62_105_3471 : ∀ z∈source105.plan.table,z.1.Valid 62 3471 := by decide +kernel
private theorem range62From28143To3474 : Segment 62 28143 29010 3471 3474 :=
  paid (pc:=74) (v:=470971191029) (by decide) source105_valid tests62_105_3471 fee62_105_29010 (by decide +kernel)

private theorem fee62_108_29010 :
    PopulationFees20258.bill (n:=29010) (PopulationFees20258.tabulate (29010-1) 256) source108.plan.table+
      4*29010*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*388982282155 := by decide +kernel
private theorem range62From28143To3783 : Segment 62 28143 29010 3474 3783 :=
  paid (pc:=72) (v:=388982282155) (by decide) source108_valid tests62_108_3474 fee62_108_29010 (by decide +kernel)

private theorem range62From28143 : Win 62 28143 29010 :=
  complete (by decide) (by decide) (join_population (join_population range62From28143To3326 range62From28143To3471) (join_population range62From28143To3474 range62From28143To3783))

private theorem fee62_110_29994 :
    PopulationFees20258.bill (n:=29994) (PopulationFees20258.tabulate (29994-1) 256) source110.plan.table+
      4*29994*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*335876349239 := by decide +kernel
private theorem range62From29011To3348 : Segment 62 29011 29994 0 3348 :=
  paid (pc:=75) (v:=335876349239) (by decide) source110_valid tests62_110_0 fee62_110_29994 (by decide +kernel)

private theorem tests62_105_3348 : ∀ z∈source105.plan.table,z.1.Valid 62 3348 := by decide +kernel
private theorem fee62_105_29994 :
    PopulationFees20258.bill (n:=29994) (PopulationFees20258.tabulate (29994-1) 256) source105.plan.table+
      4*29994*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*500643476454 := by decide +kernel
private theorem range62From29011To3471 : Segment 62 29011 29994 3348 3471 :=
  paid (pc:=74) (v:=500643476454) (by decide) source105_valid tests62_105_3348 fee62_105_29994 (by decide +kernel)

private theorem range62From29011To3474 : Segment 62 29011 29994 3471 3474 :=
  paid (pc:=74) (v:=500643476454) (by decide) source105_valid tests62_105_3471 fee62_105_29994 (by decide +kernel)

private theorem fee62_108_29994 :
    PopulationFees20258.bill (n:=29994) (PopulationFees20258.tabulate (29994-1) 256) source108.plan.table+
      4*29994*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*414041558887 := by decide +kernel
private theorem range62From29011To3762 : Segment 62 29011 29994 3474 3762 :=
  paid (pc:=72) (v:=414041558887) (by decide) source108_valid tests62_108_3474 fee62_108_29994 (by decide +kernel)

private theorem tests62_112_3762 : ∀ z∈source112.plan.table,z.1.Valid 62 3762 := by decide +kernel
private theorem fee62_112_29994 :
    PopulationFees20258.bill (n:=29994) (PopulationFees20258.tabulate (29994-1) 256) source112.plan.table+
      4*29994*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*432797433893 := by decide +kernel
private theorem range62From29011To3783 : Segment 62 29011 29994 3762 3783 :=
  paid (pc:=71) (v:=432797433893) (by decide) source112_valid tests62_112_3762 fee62_112_29994 (by decide +kernel)

private theorem range62From29011 : Win 62 29011 29994 :=
  complete (by decide) (by decide) (join_population (join_population range62From29011To3348 range62From29011To3471) (join_population range62From29011To3474 (join_population range62From29011To3762 range62From29011To3783)))

private theorem fee62_110_31131 :
    PopulationFees20258.bill (n:=31131) (PopulationFees20258.tabulate (31131-1) 256) source110.plan.table+
      4*31131*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*359877816768 := by decide +kernel
private theorem range62From29995To3371 : Segment 62 29995 31131 0 3371 :=
  paid (pc:=75) (v:=359877816768) (by decide) source110_valid tests62_110_0 fee62_110_31131 (by decide +kernel)

private theorem tests62_105_3371 : ∀ z∈source105.plan.table,z.1.Valid 62 3371 := by decide +kernel
private theorem fee62_105_31131 :
    PopulationFees20258.bill (n:=31131) (PopulationFees20258.tabulate (31131-1) 256) source105.plan.table+
      4*31131*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*536145163692 := by decide +kernel
private theorem range62From29995To3472 : Segment 62 29995 31131 3371 3472 :=
  paid (pc:=74) (v:=536145163692) (by decide) source105_valid tests62_105_3371 fee62_105_31131 (by decide +kernel)

private theorem tests62_105_3472 : ∀ z∈source105.plan.table,z.1.Valid 62 3472 := by decide +kernel
private theorem range62From29995To3474 : Segment 62 29995 31131 3472 3474 :=
  paid (pc:=74) (v:=536145163692) (by decide) source105_valid tests62_105_3472 fee62_105_31131 (by decide +kernel)

private theorem fee62_108_31131 :
    PopulationFees20258.bill (n:=31131) (PopulationFees20258.tabulate (31131-1) 256) source108.plan.table+
      4*31131*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*443689140623 := by decide +kernel
private theorem range62From29995To3746 : Segment 62 29995 31131 3474 3746 :=
  paid (pc:=73) (v:=443689140623) (by decide) source108_valid tests62_108_3474 fee62_108_31131 (by decide +kernel)

private theorem tests62_112_3746 : ∀ z∈source112.plan.table,z.1.Valid 62 3746 := by decide +kernel
private theorem fee62_112_31131 :
    PopulationFees20258.bill (n:=31131) (PopulationFees20258.tabulate (31131-1) 256) source112.plan.table+
      4*31131*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*463675693330 := by decide +kernel
private theorem range62From29995To3783 : Segment 62 29995 31131 3746 3783 :=
  paid (pc:=72) (v:=463675693330) (by decide) source112_valid tests62_112_3746 fee62_112_31131 (by decide +kernel)

private theorem range62From29995 : Win 62 29995 31131 :=
  complete (by decide) (by decide) (join_population (join_population range62From29995To3371 range62From29995To3472) (join_population range62From29995To3474 (join_population range62From29995To3746 range62From29995To3783)))

theorem cut62From26637 : Win 62 26637 31131 :=
  (join_ground (join_ground range62From26637 range62From27361) (join_ground range62From28143 (join_ground range62From29011 range62From29995)))

end JSP233.FiniteCutRanges20258
