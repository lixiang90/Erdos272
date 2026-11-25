module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source117

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests66_117_0 : ∀ z∈source117.plan.table,z.1.Valid 66 0 := by decide +kernel
private theorem fee66_117_34104 :
    PopulationFees20258.bill (n:=34104) (PopulationFees20258.tabulate (34104-1) 256) source117.plan.table+
      4*34104*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*487110785846 := by decide +kernel
private theorem range66From33181To4082 : Segment 66 33181 34104 0 4082 :=
  paid (pc:=74) (v:=487110785846) (by decide) source117_valid tests66_117_0 fee66_117_34104 (by decide +kernel)

private theorem tests66_112_4082 : ∀ z∈source112.plan.table,z.1.Valid 66 4082 := by decide +kernel
private theorem fee66_112_34104 :
    PopulationFees20258.bill (n:=34104) (PopulationFees20258.tabulate (34104-1) 256) source112.plan.table+
      4*34104*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*549848751877 := by decide +kernel
private theorem range66From33181To4287 : Segment 66 33181 34104 4082 4287 :=
  paid (pc:=73) (v:=549848751877) (by decide) source112_valid tests66_112_4082 fee66_112_34104 (by decide +kernel)

private theorem tests66_112_4287 : ∀ z∈source112.plan.table,z.1.Valid 66 4287 := by decide +kernel
private theorem range66From33181To4291 : Segment 66 33181 34104 4287 4291 :=
  paid (pc:=73) (v:=549848751877) (by decide) source112_valid tests66_112_4287 fee66_112_34104 (by decide +kernel)

private theorem range66From33181 : Win 66 33181 34104 :=
  complete (by decide) (by decide) (join_population range66From33181To4082 (join_population range66From33181To4287 range66From33181To4291))

private theorem fee66_117_35146 :
    PopulationFees20258.bill (n:=35146) (PopulationFees20258.tabulate (35146-1) 256) source117.plan.table+
      4*35146*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*515186363271 := by decide +kernel
private theorem range66From34105To4100 : Segment 66 34105 35146 0 4100 :=
  paid (pc:=74) (v:=515186363271) (by decide) source117_valid tests66_117_0 fee66_117_35146 (by decide +kernel)

private theorem tests66_112_4100 : ∀ z∈source112.plan.table,z.1.Valid 66 4100 := by decide +kernel
private theorem fee66_112_35146 :
    PopulationFees20258.bill (n:=35146) (PopulationFees20258.tabulate (35146-1) 256) source112.plan.table+
      4*35146*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*581716458509 := by decide +kernel
private theorem range66From34105To4288 : Segment 66 34105 35146 4100 4288 :=
  paid (pc:=74) (v:=581716458509) (by decide) source112_valid tests66_112_4100 fee66_112_35146 (by decide +kernel)

private theorem tests66_112_4288 : ∀ z∈source112.plan.table,z.1.Valid 66 4288 := by decide +kernel
private theorem range66From34105To4291 : Segment 66 34105 35146 4288 4291 :=
  paid (pc:=74) (v:=581716458509) (by decide) source112_valid tests66_112_4288 fee66_112_35146 (by decide +kernel)

private theorem range66From34105 : Win 66 34105 35146 :=
  complete (by decide) (by decide) (join_population range66From34105To4100 (join_population range66From34105To4288 range66From34105To4291))

private theorem fee66_117_36348 :
    PopulationFees20258.bill (n:=36348) (PopulationFees20258.tabulate (36348-1) 256) source117.plan.table+
      4*36348*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*548609091458 := by decide +kernel
private theorem range66From35147To4117 : Segment 66 35147 36348 0 4117 :=
  paid (pc:=75) (v:=548609091458) (by decide) source117_valid tests66_117_0 fee66_117_36348 (by decide +kernel)

private theorem tests66_112_4117 : ∀ z∈source112.plan.table,z.1.Valid 66 4117 := by decide +kernel
private theorem fee66_112_36348 :
    PopulationFees20258.bill (n:=36348) (PopulationFees20258.tabulate (36348-1) 256) source112.plan.table+
      4*36348*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*619694820288 := by decide +kernel
private theorem range66From35147To4288 : Segment 66 35147 36348 4117 4288 :=
  paid (pc:=74) (v:=619694820288) (by decide) source112_valid tests66_112_4117 fee66_112_36348 (by decide +kernel)

private theorem range66From35147To4291 : Segment 66 35147 36348 4288 4291 :=
  paid (pc:=74) (v:=619694820288) (by decide) source112_valid tests66_112_4288 fee66_112_36348 (by decide +kernel)

private theorem range66From35147 : Win 66 35147 36348 :=
  complete (by decide) (by decide) (join_population range66From35147To4117 (join_population range66From35147To4288 range66From35147To4291))

private theorem fee66_117_37760 :
    PopulationFees20258.bill (n:=37760) (PopulationFees20258.tabulate (37760-1) 256) source117.plan.table+
      4*37760*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*589226506585 := by decide +kernel
private theorem range66From36349To4135 : Segment 66 36349 37760 0 4135 :=
  paid (pc:=75) (v:=589226506585) (by decide) source117_valid tests66_117_0 fee66_117_37760 (by decide +kernel)

private theorem tests66_112_4135 : ∀ z∈source112.plan.table,z.1.Valid 66 4135 := by decide +kernel
private theorem fee66_112_37760 :
    PopulationFees20258.bill (n:=37760) (PopulationFees20258.tabulate (37760-1) 256) source112.plan.table+
      4*37760*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*665957625805 := by decide +kernel
private theorem range66From36349To4288 : Segment 66 36349 37760 4135 4288 :=
  paid (pc:=74) (v:=665957625805) (by decide) source112_valid tests66_112_4135 fee66_112_37760 (by decide +kernel)

private theorem range66From36349To4291 : Segment 66 36349 37760 4288 4291 :=
  paid (pc:=74) (v:=665957625805) (by decide) source112_valid tests66_112_4288 fee66_112_37760 (by decide +kernel)

private theorem range66From36349 : Win 66 36349 37760 :=
  complete (by decide) (by decide) (join_population range66From36349To4135 (join_population range66From36349To4288 range66From36349To4291))

private theorem fee66_117_39456 :
    PopulationFees20258.bill (n:=39456) (PopulationFees20258.tabulate (39456-1) 256) source117.plan.table+
      4*39456*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*639888018172 := by decide +kernel
private theorem range66From37761To4153 : Segment 66 37761 39456 0 4153 :=
  paid (pc:=75) (v:=639888018172) (by decide) source117_valid tests66_117_0 fee66_117_39456 (by decide +kernel)

private theorem tests66_112_4153 : ∀ z∈source112.plan.table,z.1.Valid 66 4153 := by decide +kernel
private theorem fee66_112_39456 :
    PopulationFees20258.bill (n:=39456) (PopulationFees20258.tabulate (39456-1) 256) source112.plan.table+
      4*39456*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*723343444017 := by decide +kernel
private theorem range66From37761To4288 : Segment 66 37761 39456 4153 4288 :=
  paid (pc:=74) (v:=723343444017) (by decide) source112_valid tests66_112_4153 fee66_112_39456 (by decide +kernel)

private theorem range66From37761To4291 : Segment 66 37761 39456 4288 4291 :=
  paid (pc:=74) (v:=723343444017) (by decide) source112_valid tests66_112_4288 fee66_112_39456 (by decide +kernel)

private theorem range66From37761 : Win 66 37761 39456 :=
  complete (by decide) (by decide) (join_population range66From37761To4153 (join_population range66From37761To4288 range66From37761To4291))

private theorem range66From39457Price : ( .marked ⟨66,182,26,10000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range66From39457 : Win 66 39457 39999 :=
  classical_route (pc:=80) range66From39457Price (by decide +kernel)

theorem cut66From33181 : Win 66 33181 39999 :=
  (join_ground (join_ground range66From33181 (join_ground range66From34105 range66From35147)) (join_ground range66From36349 (join_ground range66From37761 range66From39457)))

end JSP233.FiniteCutRanges20258
