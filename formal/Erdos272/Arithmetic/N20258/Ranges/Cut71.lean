module

public import Erdos272.Arithmetic.N20258.Ranges.Cut71From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut71From34865

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut71 : Win 71 20258 39999 :=
  (join_ground cut71From20258 cut71From34865)

end JSP233.FiniteCutRanges20258
