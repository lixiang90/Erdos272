module

public import Erdos272.Arithmetic.N20258.Ranges.Cut62From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut62From23289
public import Erdos272.Arithmetic.N20258.Ranges.Cut62From26637
public import Erdos272.Arithmetic.N20258.Ranges.Cut62From31132

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut62 : Win 62 20258 39999 :=
  (join_ground (join_ground cut62From20258 cut62From23289) (join_ground cut62From26637 cut62From31132))

end JSP233.FiniteCutRanges20258
