module

public import Erdos272.Arithmetic.N20258.Ranges.Cut50From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut50From20689
public import Erdos272.Arithmetic.N20258.Ranges.Cut50From21289
public import Erdos272.Arithmetic.N20258.Ranges.Cut50From22686
public import Erdos272.Arithmetic.N20258.Ranges.Cut50From26561

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut50 : Win 50 20258 39999 :=
  (join_ground (join_ground cut50From20258 cut50From20689) (join_ground cut50From21289 (join_ground cut50From22686 cut50From26561)))

end JSP233.FiniteCutRanges20258
