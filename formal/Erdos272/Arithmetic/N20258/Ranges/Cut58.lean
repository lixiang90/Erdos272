module

public import Erdos272.Arithmetic.N20258.Ranges.Cut58From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut58From21701
public import Erdos272.Arithmetic.N20258.Ranges.Cut58From23589
public import Erdos272.Arithmetic.N20258.Ranges.Cut58From26733
public import Erdos272.Arithmetic.N20258.Ranges.Cut58From34253

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut58 : Win 58 20258 39999 :=
  (join_ground (join_ground cut58From20258 cut58From21701) (join_ground cut58From23589 (join_ground cut58From26733 cut58From34253)))

end JSP233.FiniteCutRanges20258
