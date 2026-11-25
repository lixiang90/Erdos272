module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source003
public import Erdos272.Arithmetic.N20258.Sources.Source004
public import Erdos272.Arithmetic.N20258.Sources.Source005
public import Erdos272.Arithmetic.N20258.Sources.Source006

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests47_003_0 : ∀ z∈source003.plan.table,z.1.Valid 47 0 := by decide +kernel
private theorem fee47_003_24304 :
    PopulationFees20258.bill (n:=24304) (PopulationFees20258.tabulate (24304-1) 256) source003.plan.table+
      4*24304*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*99821718810 := by decide +kernel
private theorem range47From23167To2089 : Segment 47 23167 24304 0 2089 :=
  paid (pc:=78) (v:=99821718810) (by decide) source003_valid tests47_003_0 fee47_003_24304 (by decide +kernel)

private theorem tests47_004_2089 : ∀ z∈source004.plan.table,z.1.Valid 47 2089 := by decide +kernel
private theorem fee47_004_24304 :
    PopulationFees20258.bill (n:=24304) (PopulationFees20258.tabulate (24304-1) 256) source004.plan.table+
      4*24304*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*185778030680 := by decide +kernel
private theorem range47From23167To2133 : Segment 47 23167 24304 2089 2133 :=
  paid (pc:=77) (v:=185778030680) (by decide) source004_valid tests47_004_2089 fee47_004_24304 (by decide +kernel)

private theorem tests47_005_2133 : ∀ z∈source005.plan.table,z.1.Valid 47 2133 := by decide +kernel
private theorem fee47_005_24304 :
    PopulationFees20258.bill (n:=24304) (PopulationFees20258.tabulate (24304-1) 256) source005.plan.table+
      4*24304*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*231540065134 := by decide +kernel
private theorem range47From23167To2151 : Segment 47 23167 24304 2133 2151 :=
  paid (pc:=77) (v:=231540065134) (by decide) source005_valid tests47_005_2133 fee47_005_24304 (by decide +kernel)

private theorem tests47_006_2151 : ∀ z∈source006.plan.table,z.1.Valid 47 2151 := by decide +kernel
private theorem fee47_006_24304 :
    PopulationFees20258.bill (n:=24304) (PopulationFees20258.tabulate (24304-1) 256) source006.plan.table+
      4*24304*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*222224941434 := by decide +kernel
private theorem range47From23167To2163 : Segment 47 23167 24304 2151 2163 :=
  paid (pc:=77) (v:=222224941434) (by decide) source006_valid tests47_006_2151 fee47_006_24304 (by decide +kernel)

private theorem range47From23167 : Win 47 23167 24304 :=
  complete (by decide) (by decide) (join_population (join_population range47From23167To2089 range47From23167To2133) (join_population range47From23167To2151 range47From23167To2163))

private theorem fee47_003_25800 :
    PopulationFees20258.bill (n:=25800) (PopulationFees20258.tabulate (25800-1) 256) source003.plan.table+
      4*25800*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*111813604659 := by decide +kernel
private theorem range47From24305To2113 : Segment 47 24305 25800 0 2113 :=
  paid (pc:=77) (v:=111813604659) (by decide) source003_valid tests47_003_0 fee47_003_25800 (by decide +kernel)

private theorem tests47_005_2113 : ∀ z∈source005.plan.table,z.1.Valid 47 2113 := by decide +kernel
private theorem fee47_005_25800 :
    PopulationFees20258.bill (n:=25800) (PopulationFees20258.tabulate (25800-1) 256) source005.plan.table+
      4*25800*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*258875448724 := by decide +kernel
private theorem range47From24305To2151 : Segment 47 24305 25800 2113 2151 :=
  paid (pc:=77) (v:=258875448724) (by decide) source005_valid tests47_005_2113 fee47_005_25800 (by decide +kernel)

private theorem fee47_006_25800 :
    PopulationFees20258.bill (n:=25800) (PopulationFees20258.tabulate (25800-1) 256) source006.plan.table+
      4*25800*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*248520655809 := by decide +kernel
private theorem range47From24305To2163 : Segment 47 24305 25800 2151 2163 :=
  paid (pc:=77) (v:=248520655809) (by decide) source006_valid tests47_006_2151 fee47_006_25800 (by decide +kernel)

private theorem range47From24305 : Win 47 24305 25800 :=
  complete (by decide) (by decide) (join_population range47From24305To2113 (join_population range47From24305To2151 range47From24305To2163))

private theorem range47From25801 : Win 47 25801 39999 :=
  short (by decide) (by decide)

theorem cut47From23167 : Win 47 23167 39999 :=
  (join_ground range47From23167 (join_ground range47From24305 range47From25801))

end JSP233.FiniteCutRanges20258
