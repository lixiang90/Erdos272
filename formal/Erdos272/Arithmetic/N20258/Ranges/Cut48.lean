module

public import Erdos272.Arithmetic.N20258.Ranges.Cut48From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut48From22001

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut48 : Win 48 20258 39999 :=
  (join_ground cut48From20258 cut48From22001)

end JSP233.FiniteCutRanges20258
