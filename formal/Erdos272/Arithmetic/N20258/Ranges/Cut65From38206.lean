module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source116

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests65_116_0 : ∀ z∈source116.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_116_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source116.plan.table+
      4*39999*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*584363240392 := by decide +kernel
private theorem range65From38206To4038 : Segment 65 38206 39999 0 4038 :=
  paid (pc:=75) (v:=584363240392) (by decide) source116_valid tests65_116_0 fee65_116_39999 (by decide +kernel)

private theorem tests65_112_4038 : ∀ z∈source112.plan.table,z.1.Valid 65 4038 := by decide +kernel
private theorem fee65_112_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source112.plan.table+
      4*39999*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*742227428753 := by decide +kernel
private theorem range65From38206To4161 : Segment 65 38206 39999 4038 4161 :=
  paid (pc:=74) (v:=742227428753) (by decide) source112_valid tests65_112_4038 fee65_112_39999 (by decide +kernel)

private theorem range65From38206 : Win 65 38206 39999 :=
  complete (by decide) (by decide) (join_population range65From38206To4038 range65From38206To4161)

theorem cut65From38206 : Win 65 38206 39999 :=
  range65From38206

end JSP233.FiniteCutRanges20258
