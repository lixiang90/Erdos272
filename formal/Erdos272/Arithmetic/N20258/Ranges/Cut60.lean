module

public import Erdos272.Arithmetic.N20258.Ranges.Cut60From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut60From22306
public import Erdos272.Arithmetic.N20258.Ranges.Cut60From24593
public import Erdos272.Arithmetic.N20258.Ranges.Cut60From28879

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut60 : Win 60 20258 39999 :=
  (join_ground (join_ground cut60From20258 cut60From22306) (join_ground cut60From24593 cut60From28879))

end JSP233.FiniteCutRanges20258
