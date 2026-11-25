module

public import Erdos272.Arithmetic.N20258.Ranges.Cut61From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut61From23028
public import Erdos272.Arithmetic.N20258.Ranges.Cut61From26041
public import Erdos272.Arithmetic.N20258.Ranges.Cut61From32349

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut61 : Win 61 20258 39999 :=
  (join_ground (join_ground cut61From20258 cut61From23028) (join_ground cut61From26041 cut61From32349))

end JSP233.FiniteCutRanges20258
