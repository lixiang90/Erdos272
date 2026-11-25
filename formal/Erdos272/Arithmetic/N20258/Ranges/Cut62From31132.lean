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
private theorem fee62_110_32476 :
    PopulationFees20258.bill (n:=32476) (PopulationFees20258.tabulate (32476-1) 256) source110.plan.table+
      4*32476*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*389448798762 := by decide +kernel
private theorem range62From31132To3393 : Segment 62 31132 32476 0 3393 :=
  paid (pc:=75) (v:=389448798762) (by decide) source110_valid tests62_110_0 fee62_110_32476 (by decide +kernel)

private theorem tests62_105_3393 : ∀ z∈source105.plan.table,z.1.Valid 62 3393 := by decide +kernel
private theorem fee62_105_32476 :
    PopulationFees20258.bill (n:=32476) (PopulationFees20258.tabulate (32476-1) 256) source105.plan.table+
      4*32476*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*579749423819 := by decide +kernel
private theorem range62From31132To3472 : Segment 62 31132 32476 3393 3472 :=
  paid (pc:=75) (v:=579749423819) (by decide) source105_valid tests62_105_3393 fee62_105_32476 (by decide +kernel)

private theorem tests62_105_3472 : ∀ z∈source105.plan.table,z.1.Valid 62 3472 := by decide +kernel
private theorem range62From31132To3474 : Segment 62 31132 32476 3472 3474 :=
  paid (pc:=75) (v:=579749423819) (by decide) source105_valid tests62_105_3472 fee62_105_32476 (by decide +kernel)

private theorem tests62_108_3474 : ∀ z∈source108.plan.table,z.1.Valid 62 3474 := by decide +kernel
private theorem fee62_108_32476 :
    PopulationFees20258.bill (n:=32476) (PopulationFees20258.tabulate (32476-1) 256) source108.plan.table+
      4*32476*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*479947312848 := by decide +kernel
private theorem range62From31132To3730 : Segment 62 31132 32476 3474 3730 :=
  paid (pc:=73) (v:=479947312848) (by decide) source108_valid tests62_108_3474 fee62_108_32476 (by decide +kernel)

private theorem tests62_112_3730 : ∀ z∈source112.plan.table,z.1.Valid 62 3730 := by decide +kernel
private theorem fee62_112_32476 :
    PopulationFees20258.bill (n:=32476) (PopulationFees20258.tabulate (32476-1) 256) source112.plan.table+
      4*32476*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*501691212321 := by decide +kernel
private theorem range62From31132To3783 : Segment 62 31132 32476 3730 3783 :=
  paid (pc:=72) (v:=501691212321) (by decide) source112_valid tests62_112_3730 fee62_112_32476 (by decide +kernel)

private theorem range62From31132 : Win 62 31132 32476 :=
  complete (by decide) (by decide) (join_population (join_population range62From31132To3393 range62From31132To3472) (join_population range62From31132To3474 (join_population range62From31132To3730 range62From31132To3783)))

private theorem fee62_110_34100 :
    PopulationFees20258.bill (n:=34100) (PopulationFees20258.tabulate (34100-1) 256) source110.plan.table+
      4*34100*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*426700168002 := by decide +kernel
private theorem range62From32477To3416 : Segment 62 32477 34100 0 3416 :=
  paid (pc:=75) (v:=426700168002) (by decide) source110_valid tests62_110_0 fee62_110_34100 (by decide +kernel)

private theorem tests62_105_3416 : ∀ z∈source105.plan.table,z.1.Valid 62 3416 := by decide +kernel
private theorem fee62_105_34100 :
    PopulationFees20258.bill (n:=34100) (PopulationFees20258.tabulate (34100-1) 256) source105.plan.table+
      4*34100*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*634751203989 := by decide +kernel
private theorem range62From32477To3473 : Segment 62 32477 34100 3416 3473 :=
  paid (pc:=75) (v:=634751203989) (by decide) source105_valid tests62_105_3416 fee62_105_34100 (by decide +kernel)

private theorem tests62_105_3473 : ∀ z∈source105.plan.table,z.1.Valid 62 3473 := by decide +kernel
private theorem range62From32477To3474 : Segment 62 32477 34100 3473 3474 :=
  paid (pc:=75) (v:=634751203989) (by decide) source105_valid tests62_105_3473 fee62_105_34100 (by decide +kernel)

private theorem fee62_108_34100 :
    PopulationFees20258.bill (n:=34100) (PopulationFees20258.tabulate (34100-1) 256) source108.plan.table+
      4*34100*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*525771470735 := by decide +kernel
private theorem range62From32477To3715 : Segment 62 32477 34100 3474 3715 :=
  paid (pc:=73) (v:=525771470735) (by decide) source108_valid tests62_108_3474 fee62_108_34100 (by decide +kernel)

private theorem tests62_112_3715 : ∀ z∈source112.plan.table,z.1.Valid 62 3715 := by decide +kernel
private theorem fee62_112_34100 :
    PopulationFees20258.bill (n:=34100) (PopulationFees20258.tabulate (34100-1) 256) source112.plan.table+
      4*34100*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*549614232796 := by decide +kernel
private theorem range62From32477To3783 : Segment 62 32477 34100 3715 3783 :=
  paid (pc:=73) (v:=549614232796) (by decide) source112_valid tests62_112_3715 fee62_112_34100 (by decide +kernel)

private theorem range62From32477 : Win 62 32477 34100 :=
  complete (by decide) (by decide) (join_population (join_population range62From32477To3416 range62From32477To3473) (join_population range62From32477To3474 (join_population range62From32477To3715 range62From32477To3783)))

private theorem fee62_110_36105 :
    PopulationFees20258.bill (n:=36105) (PopulationFees20258.tabulate (36105-1) 256) source110.plan.table+
      4*36105*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*475125926651 := by decide +kernel
private theorem range62From34101To3441 : Segment 62 34101 36105 0 3441 :=
  paid (pc:=75) (v:=475125926651) (by decide) source110_valid tests62_110_0 fee62_110_36105 (by decide +kernel)

private theorem tests62_105_3441 : ∀ z∈source105.plan.table,z.1.Valid 62 3441 := by decide +kernel
private theorem fee62_105_36105 :
    PopulationFees20258.bill (n:=36105) (PopulationFees20258.tabulate (36105-1) 256) source105.plan.table+
      4*36105*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*706156875598 := by decide +kernel
private theorem range62From34101To3474 : Segment 62 34101 36105 3441 3474 :=
  paid (pc:=75) (v:=706156875598) (by decide) source105_valid tests62_105_3441 fee62_105_36105 (by decide +kernel)

private theorem fee62_108_36105 :
    PopulationFees20258.bill (n:=36105) (PopulationFees20258.tabulate (36105-1) 256) source108.plan.table+
      4*36105*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*585301379812 := by decide +kernel
private theorem range62From34101To3700 : Segment 62 34101 36105 3474 3700 :=
  paid (pc:=74) (v:=585301379812) (by decide) source108_valid tests62_108_3474 fee62_108_36105 (by decide +kernel)

private theorem tests62_112_3700 : ∀ z∈source112.plan.table,z.1.Valid 62 3700 := by decide +kernel
private theorem fee62_112_36105 :
    PopulationFees20258.bill (n:=36105) (PopulationFees20258.tabulate (36105-1) 256) source112.plan.table+
      4*36105*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*611938094872 := by decide +kernel
private theorem range62From34101To3783 : Segment 62 34101 36105 3700 3783 :=
  paid (pc:=73) (v:=611938094872) (by decide) source112_valid tests62_112_3700 fee62_112_36105 (by decide +kernel)

private theorem range62From34101 : Win 62 34101 36105 :=
  complete (by decide) (by decide) (join_population (join_population range62From34101To3441 range62From34101To3474) (join_population range62From34101To3700 range62From34101To3783))

private theorem fee62_110_38640 :
    PopulationFees20258.bill (n:=38640) (PopulationFees20258.tabulate (38640-1) 256) source110.plan.table+
      4*38640*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*539860089190 := by decide +kernel
private theorem range62From36106To3468 : Segment 62 36106 38640 0 3468 :=
  paid (pc:=75) (v:=539860089190) (by decide) source110_valid tests62_110_0 fee62_110_38640 (by decide +kernel)

private theorem tests62_105_3468 : ∀ z∈source105.plan.table,z.1.Valid 62 3468 := by decide +kernel
private theorem fee62_105_38640 :
    PopulationFees20258.bill (n:=38640) (PopulationFees20258.tabulate (38640-1) 256) source105.plan.table+
      4*38640*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*801679201978 := by decide +kernel
private theorem range62From36106To3475 : Segment 62 36106 38640 3468 3475 :=
  paid (pc:=75) (v:=801679201978) (by decide) source105_valid tests62_105_3468 fee62_105_38640 (by decide +kernel)

private theorem tests62_108_3475 : ∀ z∈source108.plan.table,z.1.Valid 62 3475 := by decide +kernel
private theorem fee62_108_38640 :
    PopulationFees20258.bill (n:=38640) (PopulationFees20258.tabulate (38640-1) 256) source108.plan.table+
      4*38640*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*665172494690 := by decide +kernel
private theorem range62From36106To3688 : Segment 62 36106 38640 3475 3688 :=
  paid (pc:=73) (v:=665172494690) (by decide) source108_valid tests62_108_3475 fee62_108_38640 (by decide +kernel)

private theorem tests62_112_3688 : ∀ z∈source112.plan.table,z.1.Valid 62 3688 := by decide +kernel
private theorem fee62_112_38640 :
    PopulationFees20258.bill (n:=38640) (PopulationFees20258.tabulate (38640-1) 256) source112.plan.table+
      4*38640*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*695202982590 := by decide +kernel
private theorem range62From36106To3783 : Segment 62 36106 38640 3688 3783 :=
  paid (pc:=73) (v:=695202982590) (by decide) source112_valid tests62_112_3688 fee62_112_38640 (by decide +kernel)

private theorem range62From36106 : Win 62 36106 38640 :=
  complete (by decide) (by decide) (join_population (join_population range62From36106To3468 range62From36106To3475) (join_population range62From36106To3688 range62From36106To3783))

private theorem range62From38641Price : ( .marked ⟨62,163,24,8000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range62From38641 : Win 62 38641 39999 :=
  classical_route (pc:=80) range62From38641Price (by decide +kernel)

theorem cut62From31132 : Win 62 31132 39999 :=
  (join_ground (join_ground range62From31132 range62From32477) (join_ground range62From34101 (join_ground range62From36106 range62From38641)))

end JSP233.FiniteCutRanges20258
