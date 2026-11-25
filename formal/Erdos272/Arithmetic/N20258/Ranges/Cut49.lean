module

public import Erdos272.Arithmetic.N20258.Ranges.Cut49From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut49From20889
public import Erdos272.Arithmetic.N20258.Ranges.Cut49From21794
public import Erdos272.Arithmetic.N20258.Ranges.Cut49From23131
public import Erdos272.Arithmetic.N20258.Ranges.Cut49From28631

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut49 : Win 49 20258 39999 :=
  (join_ground (join_ground cut49From20258 cut49From20889) (join_ground cut49From21794 (join_ground cut49From23131 cut49From28631)))

end JSP233.FiniteCutRanges20258
