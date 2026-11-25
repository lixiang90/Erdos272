module

public import Erdos272.Arithmetic.N20258.Ranges.Cut66From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut66From27261
public import Erdos272.Arithmetic.N20258.Ranges.Cut66From33181

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut66 : Win 66 20258 39999 :=
  (join_ground cut66From20258 (join_ground cut66From27261 cut66From33181))

end JSP233.FiniteCutRanges20258
