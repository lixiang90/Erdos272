module

public import Erdos272.Arithmetic.N20258.Ranges.Cut47From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut47From23167

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut47 : Win 47 20258 39999 :=
  (join_ground cut47From20258 cut47From23167)

end JSP233.FiniteCutRanges20258
