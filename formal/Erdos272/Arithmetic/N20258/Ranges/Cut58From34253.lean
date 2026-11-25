module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source098

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests58_098_0 : ∀ z∈source098.plan.table,z.1.Valid 58 0 := by decide +kernel
private theorem fee58_098_36684 :
    PopulationFees20258.bill (n:=36684) (PopulationFees20258.tabulate (36684-1) 256) source098.plan.table+
      4*36684*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*519931708010 := by decide +kernel
private theorem range58From34253To3114 : Segment 58 34253 36684 0 3114 :=
  paid (pc:=75) (v:=519931708010) (by decide) source098_valid tests58_098_0 fee58_098_36684 (by decide +kernel)

private theorem tests58_096_3114 : ∀ z∈source096.plan.table,z.1.Valid 58 3114 := by decide +kernel
private theorem fee58_096_36684 :
    PopulationFees20258.bill (n:=36684) (PopulationFees20258.tabulate (36684-1) 256) source096.plan.table+
      4*36684*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*631410252762 := by decide +kernel
private theorem range58From34253To3303 : Segment 58 34253 36684 3114 3303 :=
  paid (pc:=74) (v:=631410252762) (by decide) source096_valid tests58_096_3114 fee58_096_36684 (by decide +kernel)

private theorem tests58_096_3303 : ∀ z∈source096.plan.table,z.1.Valid 58 3303 := by decide +kernel
private theorem range58From34253To3307 : Segment 58 34253 36684 3303 3307 :=
  paid (pc:=74) (v:=631410252762) (by decide) source096_valid tests58_096_3303 fee58_096_36684 (by decide +kernel)

private theorem range58From34253 : Win 58 34253 36684 :=
  complete (by decide) (by decide) (join_population range58From34253To3114 (join_population range58From34253To3303 range58From34253To3307))

private theorem fee58_098_39856 :
    PopulationFees20258.bill (n:=39856) (PopulationFees20258.tabulate (39856-1) 256) source098.plan.table+
      4*39856*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*608087907874 := by decide +kernel
private theorem range58From36685To3149 : Segment 58 36685 39856 0 3149 :=
  paid (pc:=75) (v:=608087907874) (by decide) source098_valid tests58_098_0 fee58_098_39856 (by decide +kernel)

private theorem tests58_096_3149 : ∀ z∈source096.plan.table,z.1.Valid 58 3149 := by decide +kernel
private theorem fee58_096_39856 :
    PopulationFees20258.bill (n:=39856) (PopulationFees20258.tabulate (39856-1) 256) source096.plan.table+
      4*39856*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*738347755229 := by decide +kernel
private theorem range58From36685To3306 : Segment 58 36685 39856 3149 3306 :=
  paid (pc:=74) (v:=738347755229) (by decide) source096_valid tests58_096_3149 fee58_096_39856 (by decide +kernel)

private theorem tests58_096_3306 : ∀ z∈source096.plan.table,z.1.Valid 58 3306 := by decide +kernel
private theorem range58From36685To3307 : Segment 58 36685 39856 3306 3307 :=
  paid (pc:=74) (v:=738347755229) (by decide) source096_valid tests58_096_3306 fee58_096_39856 (by decide +kernel)

private theorem range58From36685 : Win 58 36685 39856 :=
  complete (by decide) (by decide) (join_population range58From36685To3149 (join_population range58From36685To3306 range58From36685To3307))

private theorem range58From39857 : Win 58 39857 39999 :=
  short (by decide) (by decide)

theorem cut58From34253 : Win 58 34253 39999 :=
  (join_ground range58From34253 (join_ground range58From36685 range58From39857))

end JSP233.FiniteCutRanges20258
