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

private theorem tests71_121_0 : ∀ z∈source121.plan.table,z.1.Valid 71 0 := by decide +kernel
private theorem fee71_121_37120 :
    PopulationFees20258.bill (n:=37120) (PopulationFees20258.tabulate (37120-1) 256) source121.plan.table+
      4*37120*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*567940904906 := by decide +kernel
private theorem range71From34865To4005 : Segment 71 34865 37120 0 4005 :=
  paid (pc:=72) (v:=567940904906) (by decide) source121_valid tests71_121_0 fee71_121_37120 (by decide +kernel)

private theorem tests71_119_4005 : ∀ z∈source119.plan.table,z.1.Valid 71 4005 := by decide +kernel
private theorem fee71_119_37120 :
    PopulationFees20258.bill (n:=37120) (PopulationFees20258.tabulate (37120-1) 256) source119.plan.table+
      4*37120*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1419131825647 := by decide +kernel
private theorem range71From34865To4128 : Segment 71 34865 37120 4005 4128 :=
  paid (pc:=71) (v:=1419131825647) (by decide) source119_valid tests71_119_4005 fee71_119_37120 (by decide +kernel)

private theorem tests71_119_4128 : ∀ z∈source119.plan.table,z.1.Valid 71 4128 := by decide +kernel
private theorem range71From34865To4131 : Segment 71 34865 37120 4128 4131 :=
  paid (pc:=71) (v:=1419131825647) (by decide) source119_valid tests71_119_4128 fee71_119_37120 (by decide +kernel)

private theorem tests71_122_4131 : ∀ z∈source122.plan.table,z.1.Valid 71 4131 := by decide +kernel
private theorem fee71_122_37120 :
    PopulationFees20258.bill (n:=37120) (PopulationFees20258.tabulate (37120-1) 256) source122.plan.table+
      4*37120*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1088831832153 := by decide +kernel
private theorem range71From34865To4971 : Segment 71 34865 37120 4131 4971 :=
  paid (pc:=66) (v:=1088831832153) (by decide) source122_valid tests71_122_4131 fee71_122_37120 (by decide +kernel)

private theorem range71From34865 : Win 71 34865 37120 :=
  complete (by decide) (by decide) (join_population (join_population range71From34865To4005 range71From34865To4128) (join_population range71From34865To4131 range71From34865To4971))

private theorem fee71_121_39575 :
    PopulationFees20258.bill (n:=39575) (PopulationFees20258.tabulate (39575-1) 256) source121.plan.table+
      4*39575*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*640076598155 := by decide +kernel
private theorem range71From37121To4100 : Segment 71 37121 39575 0 4100 :=
  paid (pc:=72) (v:=640076598155) (by decide) source121_valid tests71_121_0 fee71_121_39575 (by decide +kernel)

private theorem tests71_119_4100 : ∀ z∈source119.plan.table,z.1.Valid 71 4100 := by decide +kernel
private theorem fee71_119_39575 :
    PopulationFees20258.bill (n:=39575) (PopulationFees20258.tabulate (39575-1) 256) source119.plan.table+
      4*39575*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1594950187830 := by decide +kernel
private theorem range71From37121To4130 : Segment 71 37121 39575 4100 4130 :=
  paid (pc:=72) (v:=1594950187830) (by decide) source119_valid tests71_119_4100 fee71_119_39575 (by decide +kernel)

private theorem tests71_122_4130 : ∀ z∈source122.plan.table,z.1.Valid 71 4130 := by decide +kernel
private theorem fee71_122_39575 :
    PopulationFees20258.bill (n:=39575) (PopulationFees20258.tabulate (39575-1) 256) source122.plan.table+
      4*39575*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1223893566949 := by decide +kernel
private theorem range71From37121To4971 : Segment 71 37121 39575 4130 4971 :=
  paid (pc:=68) (v:=1223893566949) (by decide) source122_valid tests71_122_4130 fee71_122_39575 (by decide +kernel)

private theorem range71From37121 : Win 71 37121 39575 :=
  complete (by decide) (by decide) (join_population range71From37121To4100 (join_population range71From37121To4130 range71From37121To4971))

private theorem fee71_121_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source121.plan.table+
      4*39999*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*652829297076 := by decide +kernel
private theorem range71From39576To4953 : Segment 71 39576 39999 0 4953 :=
  paid (pc:=76) (v:=652829297076) (by decide) source121_valid tests71_121_0 fee71_121_39999 (by decide +kernel)

private theorem tests71_122_4953 : ∀ z∈source122.plan.table,z.1.Valid 71 4953 := by decide +kernel
private theorem fee71_122_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source122.plan.table+
      4*39999*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*1248405800517 := by decide +kernel
private theorem range71From39576To4971 : Segment 71 39576 39999 4953 4971 :=
  paid (pc:=73) (v:=1248405800517) (by decide) source122_valid tests71_122_4953 fee71_122_39999 (by decide +kernel)

private theorem range71From39576 : Win 71 39576 39999 :=
  complete (by decide) (by decide) (join_population range71From39576To4953 range71From39576To4971)

theorem cut71From34865 : Win 71 34865 39999 :=
  (join_ground range71From34865 (join_ground range71From37121 range71From39576))

end JSP233.FiniteCutRanges20258
