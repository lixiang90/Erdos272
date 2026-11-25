module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source122
public import Erdos272.Arithmetic.N20258.Sources.Source123
public import Erdos272.Arithmetic.N20258.Sources.Source124

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem range73From20258Price : ( .marked ⟨73,208,28,13000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range73From20258 : Win 73 20258 24408 :=
  classical_route (pc:=0) range73From20258Price (by decide +kernel)

private theorem tests73_123_0 : ∀ z∈source123.plan.table,z.1.Valid 73 0 := by decide +kernel
private theorem fee73_123_29186 :
    PopulationFees20258.bill (n:=29186) (PopulationFees20258.tabulate (29186-1) 256) source123.plan.table+
      4*29186*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*722374157389 := by decide +kernel
private theorem range73From24409To5257 : Segment 73 24409 29186 0 5257 :=
  paid (pc:=65) (v:=722374157389) (by decide) source123_valid tests73_123_0 fee73_123_29186 (by decide +kernel)

private theorem range73From24409 : Win 73 24409 29186 :=
  complete (by decide) (by decide) range73From24409To5257

private theorem fee73_123_33594 :
    PopulationFees20258.bill (n:=33594) (PopulationFees20258.tabulate (33594-1) 256) source123.plan.table+
      4*33594*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*928543406231 := by decide +kernel
private theorem range73From29187To3819 : Segment 73 29187 33594 0 3819 :=
  paid (pc:=60) (v:=928543406231) (by decide) source123_valid tests73_123_0 fee73_123_33594 (by decide +kernel)

private theorem tests73_123_3819 : ∀ z∈source123.plan.table,z.1.Valid 73 3819 := by decide +kernel
private theorem range73From29187To4089 : Segment 73 29187 33594 3819 4089 :=
  paid (pc:=58) (v:=928543406231) (by decide) source123_valid tests73_123_3819 fee73_123_33594 (by decide +kernel)

private theorem tests73_123_4089 : ∀ z∈source123.plan.table,z.1.Valid 73 4089 := by decide +kernel
private theorem range73From29187To4170 : Segment 73 29187 33594 4089 4170 :=
  paid (pc:=58) (v:=928543406231) (by decide) source123_valid tests73_123_4089 fee73_123_33594 (by decide +kernel)

private theorem tests73_123_4170 : ∀ z∈source123.plan.table,z.1.Valid 73 4170 := by decide +kernel
private theorem range73From29187To4197 : Segment 73 29187 33594 4170 4197 :=
  paid (pc:=58) (v:=928543406231) (by decide) source123_valid tests73_123_4170 fee73_123_33594 (by decide +kernel)

private theorem tests73_123_4197 : ∀ z∈source123.plan.table,z.1.Valid 73 4197 := by decide +kernel
private theorem range73From29187To4258 : Segment 73 29187 33594 4197 4258 :=
  paid (pc:=57) (v:=928543406231) (by decide) source123_valid tests73_123_4197 fee73_123_33594 (by decide +kernel)

private theorem tests73_122_4258 : ∀ z∈source122.plan.table,z.1.Valid 73 4258 := by decide +kernel
private theorem fee73_122_33594 :
    PopulationFees20258.bill (n:=33594) (PopulationFees20258.tabulate (33594-1) 256) source122.plan.table+
      4*33594*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*908897412940 := by decide +kernel
private theorem range73From29187To5257 : Segment 73 29187 33594 4258 5257 :=
  paid (pc:=56) (v:=908897412940) (by decide) source122_valid tests73_122_4258 fee73_122_33594 (by decide +kernel)

private theorem range73From29187 : Win 73 29187 33594 :=
  complete (by decide) (by decide) (join_population (join_population range73From29187To3819 (join_population range73From29187To4089 range73From29187To4170)) (join_population range73From29187To4197 (join_population range73From29187To4258 range73From29187To5257)))

private theorem fee73_123_37290 :
    PopulationFees20258.bill (n:=37290) (PopulationFees20258.tabulate (37290-1) 256) source123.plan.table+
      4*37290*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*1121272995466 := by decide +kernel
private theorem range73From33595To4263 : Segment 73 33595 37290 0 4263 :=
  paid (pc:=65) (v:=1121272995466) (by decide) source123_valid tests73_123_0 fee73_123_37290 (by decide +kernel)

private theorem tests73_122_4263 : ∀ z∈source122.plan.table,z.1.Valid 73 4263 := by decide +kernel
private theorem fee73_122_37290 :
    PopulationFees20258.bill (n:=37290) (PopulationFees20258.tabulate (37290-1) 256) source122.plan.table+
      4*37290*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1098265051699 := by decide +kernel
private theorem range73From33595To4445 : Segment 73 33595 37290 4263 4445 :=
  paid (pc:=64) (v:=1098265051699) (by decide) source122_valid tests73_122_4263 fee73_122_37290 (by decide +kernel)

private theorem tests73_122_4445 : ∀ z∈source122.plan.table,z.1.Valid 73 4445 := by decide +kernel
private theorem range73From33595To4452 : Segment 73 33595 37290 4445 4452 :=
  paid (pc:=64) (v:=1098265051699) (by decide) source122_valid tests73_122_4445 fee73_122_37290 (by decide +kernel)

private theorem tests73_124_4452 : ∀ z∈source124.plan.table,z.1.Valid 73 4452 := by decide +kernel
private theorem fee73_124_37290 :
    PopulationFees20258.bill (n:=37290) (PopulationFees20258.tabulate (37290-1) 256) source124.plan.table+
      4*37290*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*944102499563 := by decide +kernel
private theorem range73From33595To5257 : Segment 73 33595 37290 4452 5257 :=
  paid (pc:=59) (v:=944102499563) (by decide) source124_valid tests73_124_4452 fee73_124_37290 (by decide +kernel)

private theorem range73From33595 : Win 73 33595 37290 :=
  complete (by decide) (by decide) (join_population (join_population range73From33595To4263 range73From33595To4445) (join_population range73From33595To4452 range73From33595To5257))

private theorem fee73_123_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source123.plan.table+
      4*39999*NaturalPopulation20258.weights source123.extras≤source123.plan.scale*1273573311943 := by decide +kernel
private theorem range73From37291To4942 : Segment 73 37291 39999 0 4942 :=
  paid (pc:=68) (v:=1273573311943) (by decide) source123_valid tests73_123_0 fee73_123_39999 (by decide +kernel)

private theorem tests73_124_4942 : ∀ z∈source124.plan.table,z.1.Valid 73 4942 := by decide +kernel
private theorem fee73_124_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source124.plan.table+
      4*39999*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*1073167307727 := by decide +kernel
private theorem range73From37291To5257 : Segment 73 37291 39999 4942 5257 :=
  paid (pc:=65) (v:=1073167307727) (by decide) source124_valid tests73_124_4942 fee73_124_39999 (by decide +kernel)

private theorem range73From37291 : Win 73 37291 39999 :=
  complete (by decide) (by decide) (join_population range73From37291To4942 range73From37291To5257)

theorem cut73From20258 : Win 73 20258 39999 :=
  (join_ground (join_ground range73From20258 range73From24409) (join_ground range73From29187 (join_ground range73From33595 range73From37291)))

end JSP233.FiniteCutRanges20258
