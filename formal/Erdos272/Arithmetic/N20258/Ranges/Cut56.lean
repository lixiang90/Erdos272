module

public import Erdos272.Arithmetic.N20258.Ranges.Cut56From20258
public import Erdos272.Arithmetic.N20258.Ranges.Cut56From20797
public import Erdos272.Arithmetic.N20258.Ranges.Cut56From21487
public import Erdos272.Arithmetic.N20258.Ranges.Cut56From22699
public import Erdos272.Arithmetic.N20258.Ranges.Cut56From24657
public import Erdos272.Arithmetic.N20258.Ranges.Cut56From28929

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

theorem cut56 : Win 56 20258 39999 :=
  (join_ground (join_ground cut56From20258 (join_ground cut56From20797 cut56From21487)) (join_ground cut56From22699 (join_ground cut56From24657 cut56From28929)))

end JSP233.FiniteCutRanges20258
