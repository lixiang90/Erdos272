module

public import Erdos272.Arithmetic.N20258.Ranges.Cut64From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut64From25061
public import Erdos272.Arithmetic.N20258.Ranges.Cut64From29419
public import Erdos272.Arithmetic.N20258.Ranges.Cut64From38609

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut64 : Win 64 20258 39999 :=
  (join_ground (join_ground cut64From20258 cut64From25061) (join_ground cut64From29419 cut64From38609))

end JSP233.FiniteCutRanges20258
