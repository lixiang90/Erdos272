module

public import Erdos272.Counting.N19227.FiniteCuts19227

@[expose] public section
namespace JSP233.Credit19227
open FiniteCuts19227 PopulationRanges20258 ConcentratedBlocks20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private def s66 : Source := .marked ⟨66,199,29,12000⟩
private theorem s66_valid : s66.Valid := by decide +kernel

private theorem band66From19227 : Band 66 76 19227 19448 :=
  large (q:=s66) (pc:=0) (by decide) (by decide) (by decide) s66_valid (by decide +kernel)
private theorem band66From19449 : Band 66 76 19449 19682 :=
  large (q:=s66) (pc:=0) (by decide) (by decide) (by decide) s66_valid (by decide +kernel)

theorem band66 : Band 66 76 19227 19682 :=
  fun m lo hi => (join_ground (band66From19227 m lo hi) (band66From19449 m lo hi))

private def s77 : Source := .marked ⟨77,223,30,15000⟩
private theorem s77_valid : s77.Valid := by decide +kernel

private theorem band77From19227 : Band 77 237 19227 19448 :=
  large (q:=s77) (pc:=0) (by decide) (by decide) (by decide) s77_valid (by decide +kernel)
private theorem band77From19449 : Band 77 237 19449 19682 :=
  large (q:=s77) (pc:=0) (by decide) (by decide) (by decide) s77_valid (by decide +kernel)

theorem band77 : Band 77 237 19227 19682 :=
  fun m lo hi => (join_ground (band77From19227 m lo hi) (band77From19449 m lo hi))

private def s238 : Source := .uniform 238
private theorem s238_valid : s238.Valid := by decide +kernel

private theorem band238From19227 : Band 238 1655 19227 19448 :=
  large (q:=s238) (pc:=80) (by decide) (by decide) (by decide) s238_valid (by decide +kernel)
private theorem band238From19449 : Band 238 1655 19449 19682 :=
  large (q:=s238) (pc:=80) (by decide) (by decide) (by decide) s238_valid (by decide +kernel)

theorem band238 : Band 238 1655 19227 19682 :=
  fun m lo hi => (join_ground (band238From19227 m lo hi) (band238From19449 m lo hi))


end JSP233.Credit19227
