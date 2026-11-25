module

public import Erdos272.Arithmetic.N20258.Ranges.Cut63From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut63From24364
public import Erdos272.Arithmetic.N20258.Ranges.Cut63From27881
public import Erdos272.Arithmetic.N20258.Ranges.Cut63From34669

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut63 : Win 63 20258 39999 :=
  (join_ground (join_ground cut63From20258 cut63From24364) (join_ground cut63From27881 cut63From34669))

end JSP233.FiniteCutRanges20258
