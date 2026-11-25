module

public import Erdos272.Arithmetic.N20258.Ranges.Cut65From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut65From25561
public import Erdos272.Arithmetic.N20258.Ranges.Cut65From29461
public import Erdos272.Arithmetic.N20258.Ranges.Cut65From38206

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut65 : Win 65 20258 39999 :=
  (join_ground (join_ground cut65From20258 cut65From25561) (join_ground cut65From29461 cut65From38206))

end JSP233.FiniteCutRanges20258
