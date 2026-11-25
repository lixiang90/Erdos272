module

public import Erdos272.Arithmetic.N20258.Ranges.Cut67From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut67From29356

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut67 : Win 67 20258 39999 :=
  (join_ground cut67From20258 cut67From29356)

end JSP233.FiniteCutRanges20258
