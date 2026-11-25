module

public import Erdos272.Arithmetic.N20258.Ranges.Cut51From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut51From20807
public import Erdos272.Arithmetic.N20258.Ranges.Cut51From21505
public import Erdos272.Arithmetic.N20258.Ranges.Cut51From23016
public import Erdos272.Arithmetic.N20258.Ranges.Cut51From26909

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut51 : Win 51 20258 39999 :=
  (join_ground (join_ground cut51From20258 cut51From20807) (join_ground cut51From21505 (join_ground cut51From23016 cut51From26909)))

end JSP233.FiniteCutRanges20258
