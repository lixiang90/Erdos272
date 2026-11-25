module

public import Erdos272.Arithmetic.N20258.Ranges.Cut57From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut57From21066
public import Erdos272.Arithmetic.N20258.Ranges.Cut57From22201
public import Erdos272.Arithmetic.N20258.Ranges.Cut57From23653
public import Erdos272.Arithmetic.N20258.Ranges.Cut57From25763
public import Erdos272.Arithmetic.N20258.Ranges.Cut57From29020

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut57 : Win 57 20258 39999 :=
  (join_ground (join_ground cut57From20258 (join_ground cut57From21066 cut57From22201)) (join_ground cut57From23653 (join_ground cut57From25763 cut57From29020)))

end JSP233.FiniteCutRanges20258
