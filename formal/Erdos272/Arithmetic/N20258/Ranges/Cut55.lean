module

public import Erdos272.Arithmetic.N20258.Ranges.Cut55From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut55From20761
public import Erdos272.Arithmetic.N20258.Ranges.Cut55From21699
public import Erdos272.Arithmetic.N20258.Ranges.Cut55From22903
public import Erdos272.Arithmetic.N20258.Ranges.Cut55From25051
public import Erdos272.Arithmetic.N20258.Ranges.Cut55From30355

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut55 : Win 55 20258 39999 :=
  (join_ground (join_ground cut55From20258 (join_ground cut55From20761 cut55From21699)) (join_ground cut55From22903 (join_ground cut55From25051 cut55From30355)))

end JSP233.FiniteCutRanges20258
