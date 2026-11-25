module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source114

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests64_114_0 : ∀ z∈source114.plan.table,z.1.Valid 64 0 := by decide +kernel
private theorem fee64_114_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source114.plan.table+
      4*39999*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*618930712102 := by decide +kernel
private theorem range64From38609To4033 : Segment 64 38609 39999 0 4033 :=
  paid (pc:=76) (v:=618930712102) (by decide) source114_valid tests64_114_0 fee64_114_39999 (by decide +kernel)

private theorem range64From38609 : Win 64 38609 39999 :=
  complete (by decide) (by decide) range64From38609To4033

theorem cut64From38609 : Win 64 38609 39999 :=
  range64From38609

end JSP233.FiniteCutRanges20258
