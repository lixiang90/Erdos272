module

public import Erdos272.Arithmetic.N20258.Ranges.Cut68From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut68From34415

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut68 : Win 68 20258 39999 :=
  (join_ground cut68From20258 cut68From34415)

end JSP233.FiniteCutRanges20258
