module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source119
public import Erdos272.Arithmetic.N20258.Sources.Source121
public import Erdos272.Arithmetic.N20258.Sources.Source122

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests70_121_0 : ∀ z∈source121.plan.table,z.1.Valid 70 0 := by decide +kernel
private theorem fee70_121_37714 :
    PopulationFees20258.bill (n:=37714) (PopulationFees20258.tabulate (37714-1) 256) source121.plan.table+
      4*37714*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*584785598191 := by decide +kernel
private theorem range70From35342To4000 : Segment 70 35342 37714 0 4000 :=
  paid (pc:=72) (v:=584785598191) (by decide) source121_valid tests70_121_0 fee70_121_37714 (by decide +kernel)

private theorem tests70_119_4000 : ∀ z∈source119.plan.table,z.1.Valid 70 4000 := by decide +kernel
private theorem fee70_119_37714 :
    PopulationFees20258.bill (n:=37714) (PopulationFees20258.tabulate (37714-1) 256) source119.plan.table+
      4*37714*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1461095446014 := by decide +kernel
private theorem range70From35342To4070 : Segment 70 35342 37714 4000 4070 :=
  paid (pc:=71) (v:=1461095446014) (by decide) source119_valid tests70_119_4000 fee70_119_37714 (by decide +kernel)

private theorem tests70_119_4070 : ∀ z∈source119.plan.table,z.1.Valid 70 4070 := by decide +kernel
private theorem range70From35342To4072 : Segment 70 35342 37714 4070 4072 :=
  paid (pc:=71) (v:=1461095446014) (by decide) source119_valid tests70_119_4070 fee70_119_37714 (by decide +kernel)

private theorem tests70_119_4072 : ∀ z∈source119.plan.table,z.1.Valid 70 4072 := by decide +kernel
private theorem range70From35342To4075 : Segment 70 35342 37714 4072 4075 :=
  paid (pc:=71) (v:=1461095446014) (by decide) source119_valid tests70_119_4072 fee70_119_37714 (by decide +kernel)

private theorem tests70_122_4075 : ∀ z∈source122.plan.table,z.1.Valid 70 4075 := by decide +kernel
private theorem fee70_122_37714 :
    PopulationFees20258.bill (n:=37714) (PopulationFees20258.tabulate (37714-1) 256) source122.plan.table+
      4*37714*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1121005594564 := by decide +kernel
private theorem range70From35342To4831 : Segment 70 35342 37714 4075 4831 :=
  paid (pc:=67) (v:=1121005594564) (by decide) source122_valid tests70_122_4075 fee70_122_37714 (by decide +kernel)

private theorem range70From35342 : Win 70 35342 37714 :=
  complete (by decide) (by decide) (join_population (join_population range70From35342To4000 range70From35342To4070) (join_population range70From35342To4072 (join_population range70From35342To4075 range70From35342To4831)))

private theorem fee70_121_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source121.plan.table+
      4*39999*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*652829297076 := by decide +kernel
private theorem range70From37715To4204 : Segment 70 37715 39999 0 4204 :=
  paid (pc:=73) (v:=652829297076) (by decide) source121_valid tests70_121_0 fee70_121_39999 (by decide +kernel)

private theorem tests70_122_4204 : ∀ z∈source122.plan.table,z.1.Valid 70 4204 := by decide +kernel
private theorem fee70_122_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source122.plan.table+
      4*39999*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1248405800517 := by decide +kernel
private theorem range70From37715To4831 : Segment 70 37715 39999 4204 4831 :=
  paid (pc:=69) (v:=1248405800517) (by decide) source122_valid tests70_122_4204 fee70_122_39999 (by decide +kernel)

private theorem range70From37715 : Win 70 37715 39999 :=
  complete (by decide) (by decide) (join_population range70From37715To4204 range70From37715To4831)

theorem cut70From35342 : Win 70 35342 39999 :=
  (join_ground range70From35342 range70From37715)

end JSP233.FiniteCutRanges20258
