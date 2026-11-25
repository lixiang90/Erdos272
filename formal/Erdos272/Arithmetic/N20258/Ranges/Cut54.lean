module

public import Erdos272.Arithmetic.N20258.Ranges.Cut54From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut54From21009
public import Erdos272.Arithmetic.N20258.Ranges.Cut54From22013
public import Erdos272.Arithmetic.N20258.Ranges.Cut54From22917
public import Erdos272.Arithmetic.N20258.Ranges.Cut54From24879
public import Erdos272.Arithmetic.N20258.Ranges.Cut54From29521

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut54 : Win 54 20258 39999 :=
  (join_ground (join_ground cut54From20258 (join_ground cut54From21009 cut54From22013)) (join_ground cut54From22917 (join_ground cut54From24879 cut54From29521)))

end JSP233.FiniteCutRanges20258
