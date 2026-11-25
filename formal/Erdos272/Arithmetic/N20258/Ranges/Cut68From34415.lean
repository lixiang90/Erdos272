module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source119
public import Erdos272.Arithmetic.N20258.Sources.Source120

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests68_120_0 : ∀ z∈source120.plan.table,z.1.Valid 68 0 := by decide +kernel
private theorem fee68_120_36140 :
    PopulationFees20258.bill (n:=36140) (PopulationFees20258.tabulate (36140-1) 256) source120.plan.table+
      4*36140*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*570197401161 := by decide +kernel
private theorem range68From34415To4111 : Segment 68 34415 36140 0 4111 :=
  paid (pc:=72) (v:=570197401161) (by decide) source120_valid tests68_120_0 fee68_120_36140 (by decide +kernel)

private theorem tests68_119_4111 : ∀ z∈source119.plan.table,z.1.Valid 68 4111 := by decide +kernel
private theorem fee68_119_36140 :
    PopulationFees20258.bill (n:=36140) (PopulationFees20258.tabulate (36140-1) 256) source119.plan.table+
      4*36140*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1351755820481 := by decide +kernel
private theorem range68From34415To4541 : Segment 68 34415 36140 4111 4541 :=
  paid (pc:=70) (v:=1351755820481) (by decide) source119_valid tests68_119_4111 fee68_119_36140 (by decide +kernel)

private theorem tests68_119_4541 : ∀ z∈source119.plan.table,z.1.Valid 68 4541 := by decide +kernel
private theorem range68From34415To4557 : Segment 68 34415 36140 4541 4557 :=
  paid (pc:=70) (v:=1351755820481) (by decide) source119_valid tests68_119_4541 fee68_119_36140 (by decide +kernel)

private theorem range68From34415 : Win 68 34415 36140 :=
  complete (by decide) (by decide) (join_population range68From34415To4111 (join_population range68From34415To4541 range68From34415To4557))

private theorem fee68_120_37884 :
    PopulationFees20258.bill (n:=37884) (PopulationFees20258.tabulate (37884-1) 256) source120.plan.table+
      4*37884*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*622693966054 := by decide +kernel
private theorem range68From36141To4219 : Segment 68 36141 37884 0 4219 :=
  paid (pc:=73) (v:=622693966054) (by decide) source120_valid tests68_120_0 fee68_120_37884 (by decide +kernel)

private theorem tests68_119_4219 : ∀ z∈source119.plan.table,z.1.Valid 68 4219 := by decide +kernel
private theorem fee68_119_37884 :
    PopulationFees20258.bill (n:=37884) (PopulationFees20258.tabulate (37884-1) 256) source119.plan.table+
      4*37884*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1472662648606 := by decide +kernel
private theorem range68From36141To4546 : Segment 68 36141 37884 4219 4546 :=
  paid (pc:=72) (v:=1472662648606) (by decide) source119_valid tests68_119_4219 fee68_119_37884 (by decide +kernel)

private theorem tests68_119_4546 : ∀ z∈source119.plan.table,z.1.Valid 68 4546 := by decide +kernel
private theorem range68From36141To4557 : Segment 68 36141 37884 4546 4557 :=
  paid (pc:=72) (v:=1472662648606) (by decide) source119_valid tests68_119_4546 fee68_119_37884 (by decide +kernel)

private theorem range68From36141 : Win 68 36141 37884 :=
  complete (by decide) (by decide) (join_population range68From36141To4219 (join_population range68From36141To4546 range68From36141To4557))

private theorem fee68_120_39729 :
    PopulationFees20258.bill (n:=39729) (PopulationFees20258.tabulate (39729-1) 256) source120.plan.table+
      4*39729*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*680652918268 := by decide +kernel
private theorem range68From37885To4308 : Segment 68 37885 39729 0 4308 :=
  paid (pc:=74) (v:=680652918268) (by decide) source120_valid tests68_120_0 fee68_120_39729 (by decide +kernel)

private theorem tests68_119_4308 : ∀ z∈source119.plan.table,z.1.Valid 68 4308 := by decide +kernel
private theorem fee68_119_39729 :
    PopulationFees20258.bill (n:=39729) (PopulationFees20258.tabulate (39729-1) 256) source119.plan.table+
      4*39729*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1606278755868 := by decide +kernel
private theorem range68From37885To4551 : Segment 68 37885 39729 4308 4551 :=
  paid (pc:=73) (v:=1606278755868) (by decide) source119_valid tests68_119_4308 fee68_119_39729 (by decide +kernel)

private theorem tests68_119_4551 : ∀ z∈source119.plan.table,z.1.Valid 68 4551 := by decide +kernel
private theorem range68From37885To4557 : Segment 68 37885 39729 4551 4557 :=
  paid (pc:=73) (v:=1606278755868) (by decide) source119_valid tests68_119_4551 fee68_119_39729 (by decide +kernel)

private theorem range68From37885 : Win 68 37885 39729 :=
  complete (by decide) (by decide) (join_population range68From37885To4308 (join_population range68From37885To4551 range68From37885To4557))

private theorem range68From39730Price : ( .marked ⟨68,199,28,12000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range68From39730 : Win 68 39730 39999 :=
  classical_route (pc:=80) range68From39730Price (by decide +kernel)

theorem cut68From34415 : Win 68 34415 39999 :=
  (join_ground (join_ground range68From34415 range68From36141) (join_ground range68From37885 range68From39730))

end JSP233.FiniteCutRanges20258
