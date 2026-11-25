module

public import Erdos272.Arithmetic.N20258.Ranges.Cut52From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut52From20833
public import Erdos272.Arithmetic.N20258.Ranges.Cut52From21571
public import Erdos272.Arithmetic.N20258.Ranges.Cut52From22540
public import Erdos272.Arithmetic.N20258.Ranges.Cut52From24726
public import Erdos272.Arithmetic.N20258.Ranges.Cut52From30825

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut52 : Win 52 20258 39999 :=
  (join_ground (join_ground cut52From20258 (join_ground cut52From20833 cut52From21571)) (join_ground cut52From22540 (join_ground cut52From24726 cut52From30825)))

end JSP233.FiniteCutRanges20258
