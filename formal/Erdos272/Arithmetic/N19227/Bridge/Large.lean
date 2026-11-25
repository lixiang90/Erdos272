module

public import Erdos272.Counting.N19227.FiniteCuts19227

@[expose] public section
namespace JSP233.Credit19227
open FiniteCuts19227 PopulationRanges20258 ConcentratedBlocks20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private def source67 : Source := .marked ⟨67,192,27,11000⟩
private theorem valid67 : source67.Valid := by decide +kernel

private theorem band67From19683 : Band 67 76 19683 20257 :=
  large (q:=source67) (pc:=0) (by decide) (by decide) (by decide) valid67 (by decide +kernel)

theorem bridgeBand67 : Band 67 76 19683 20257 :=
  fun m lo hi => (band67From19683 m lo hi)

private def source77 : Source := .marked ⟨77,223,30,15000⟩
private theorem valid77 : source77.Valid := by decide +kernel

private theorem band77From19683 : Band 77 237 19683 20257 :=
  large (q:=source77) (pc:=0) (by decide) (by decide) (by decide) valid77 (by decide +kernel)

theorem bridgeBand77 : Band 77 237 19683 20257 :=
  fun m lo hi => (band77From19683 m lo hi)

private def source238 : Source := .uniform 238
private theorem valid238 : source238.Valid := by decide +kernel

private theorem band238From19683 : Band 238 1688 19683 19960 :=
  large (q:=source238) (pc:=82) (by decide) (by decide) (by decide) valid238 (by decide +kernel)

private theorem band238From19961 : Band 238 1688 19961 20257 :=
  large (q:=source238) (pc:=82) (by decide) (by decide) (by decide) valid238 (by decide +kernel)

theorem bridgeBand238 : Band 238 1688 19683 20257 :=
  fun m lo hi => (join_ground (band238From19683 m lo hi) (band238From19961 m lo hi))


end JSP233.Credit19227
