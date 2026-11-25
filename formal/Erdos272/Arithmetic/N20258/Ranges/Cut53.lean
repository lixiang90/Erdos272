module

public import Erdos272.Arithmetic.N20258.Ranges.Cut53From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From20539
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From20862
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From21225
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From22041
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From23542
public import Erdos272.Arithmetic.N20258.Ranges.Cut53From27073

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut53 : Win 53 20258 39999 :=
  (join_ground (join_ground cut53From20258 (join_ground cut53From20539 cut53From20862)) (join_ground (join_ground cut53From21225 cut53From22041) (join_ground cut53From23542 cut53From27073)))

end JSP233.FiniteCutRanges20258
