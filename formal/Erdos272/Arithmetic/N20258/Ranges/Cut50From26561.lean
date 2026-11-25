module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source026
public import Erdos272.Arithmetic.N20258.Sources.Source028
public import Erdos272.Arithmetic.N20258.Sources.Source033
public import Erdos272.Arithmetic.N20258.Sources.Source035

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests50_028_0 : ∀ z∈source028.plan.table,z.1.Valid 50 0 := by decide +kernel
private theorem fee50_028_28280 :
    PopulationFees20258.bill (n:=28280) (PopulationFees20258.tabulate (28280-1) 256) source028.plan.table+
      4*28280*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*164529015077 := by decide +kernel
private theorem range50From26561To2334 : Segment 50 26561 28280 0 2334 :=
  paid (pc:=77) (v:=164529015077) (by decide) source028_valid tests50_028_0 fee50_028_28280 (by decide +kernel)

private theorem tests50_033_2334 : ∀ z∈source033.plan.table,z.1.Valid 50 2334 := by decide +kernel
private theorem fee50_033_28280 :
    PopulationFees20258.bill (n:=28280) (PopulationFees20258.tabulate (28280-1) 256) source033.plan.table+
      4*28280*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*333441989381 := by decide +kernel
private theorem range50From26561To2399 : Segment 50 26561 28280 2334 2399 :=
  paid (pc:=76) (v:=333441989381) (by decide) source033_valid tests50_033_2334 fee50_033_28280 (by decide +kernel)

private theorem tests50_026_2399 : ∀ z∈source026.plan.table,z.1.Valid 50 2399 := by decide +kernel
private theorem fee50_026_28280 :
    PopulationFees20258.bill (n:=28280) (PopulationFees20258.tabulate (28280-1) 256) source026.plan.table+
      4*28280*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*329150013457 := by decide +kernel
private theorem range50From26561To2412 : Segment 50 26561 28280 2399 2412 :=
  paid (pc:=76) (v:=329150013457) (by decide) source026_valid tests50_026_2399 fee50_026_28280 (by decide +kernel)

private theorem tests50_035_2412 : ∀ z∈source035.plan.table,z.1.Valid 50 2412 := by decide +kernel
private theorem fee50_035_28280 :
    PopulationFees20258.bill (n:=28280) (PopulationFees20258.tabulate (28280-1) 256) source035.plan.table+
      4*28280*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*314619335560 := by decide +kernel
private theorem range50From26561To2451 : Segment 50 26561 28280 2412 2451 :=
  paid (pc:=76) (v:=314619335560) (by decide) source035_valid tests50_035_2412 fee50_035_28280 (by decide +kernel)

private theorem range50From26561 : Win 50 26561 28280 :=
  complete (by decide) (by decide) (join_population (join_population range50From26561To2334 range50From26561To2399) (join_population range50From26561To2412 range50From26561To2451))

private theorem range50From28281 : Win 50 28281 39999 :=
  short (by decide) (by decide)

theorem cut50From26561 : Win 50 26561 39999 :=
  (join_ground range50From26561 range50From28281)

end JSP233.FiniteCutRanges20258
