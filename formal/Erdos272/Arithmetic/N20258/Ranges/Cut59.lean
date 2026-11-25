module

public import Erdos272.Arithmetic.N20258.Ranges.Cut59From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut59From21673
public import Erdos272.Arithmetic.N20258.Ranges.Cut59From23185
public import Erdos272.Arithmetic.N20258.Ranges.Cut59From25414
public import Erdos272.Arithmetic.N20258.Ranges.Cut59From28623

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut59 : Win 59 20258 39999 :=
  (join_ground (join_ground cut59From20258 cut59From21673) (join_ground cut59From23185 (join_ground cut59From25414 cut59From28623)))

end JSP233.FiniteCutRanges20258
