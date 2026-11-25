module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source114

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests64_114_0 : ∀ z∈source114.plan.table,z.1.Valid 64 0 := by decide +kernel
private theorem fee64_114_21516 :
    PopulationFees20258.bill (n:=21516) (PopulationFees20258.tabulate (21516-1) 256) source114.plan.table+
      4*21516*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*196567081940 := by decide +kernel
private theorem range64From20258To3463 : Segment 64 20258 21516 0 3463 :=
  paid (pc:=61) (v:=196567081940) (by decide) source114_valid tests64_114_0 fee64_114_21516 (by decide +kernel)

private theorem tests64_114_3463 : ∀ z∈source114.plan.table,z.1.Valid 64 3463 := by decide +kernel
private theorem range64From20258To3576 : Segment 64 20258 21516 3463 3576 :=
  paid (pc:=60) (v:=196567081940) (by decide) source114_valid tests64_114_3463 fee64_114_21516 (by decide +kernel)

private theorem tests64_114_3576 : ∀ z∈source114.plan.table,z.1.Valid 64 3576 := by decide +kernel
private theorem range64From20258To3585 : Segment 64 20258 21516 3576 3585 :=
  paid (pc:=60) (v:=196567081940) (by decide) source114_valid tests64_114_3576 fee64_114_21516 (by decide +kernel)

private theorem tests64_108_3585 : ∀ z∈source108.plan.table,z.1.Valid 64 3585 := by decide +kernel
private theorem fee64_108_21516 :
    PopulationFees20258.bill (n:=21516) (PopulationFees20258.tabulate (21516-1) 256) source108.plan.table+
      4*21516*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*224706397355 := by decide +kernel
private theorem range64From20258To4033 : Segment 64 20258 21516 3585 4033 :=
  paid (pc:=55) (v:=224706397355) (by decide) source108_valid tests64_108_3585 fee64_108_21516 (by decide +kernel)

private theorem range64From20258 : Win 64 20258 21516 :=
  complete (by decide) (by decide) (join_population (join_population range64From20258To3463 range64From20258To3576) (join_population range64From20258To3585 range64From20258To4033))

private theorem fee64_114_22413 :
    PopulationFees20258.bill (n:=22413) (PopulationFees20258.tabulate (22413-1) 256) source114.plan.table+
      4*22413*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*211700799052 := by decide +kernel
private theorem range64From21517To3509 : Segment 64 21517 22413 0 3509 :=
  paid (pc:=65) (v:=211700799052) (by decide) source114_valid tests64_114_0 fee64_114_22413 (by decide +kernel)

private theorem tests64_114_3509 : ∀ z∈source114.plan.table,z.1.Valid 64 3509 := by decide +kernel
private theorem range64From21517To3581 : Segment 64 21517 22413 3509 3581 :=
  paid (pc:=64) (v:=211700799052) (by decide) source114_valid tests64_114_3509 fee64_114_22413 (by decide +kernel)

private theorem tests64_114_3581 : ∀ z∈source114.plan.table,z.1.Valid 64 3581 := by decide +kernel
private theorem range64From21517To3584 : Segment 64 21517 22413 3581 3584 :=
  paid (pc:=64) (v:=211700799052) (by decide) source114_valid tests64_114_3581 fee64_114_22413 (by decide +kernel)

private theorem tests64_108_3584 : ∀ z∈source108.plan.table,z.1.Valid 64 3584 := by decide +kernel
private theorem fee64_108_22413 :
    PopulationFees20258.bill (n:=22413) (PopulationFees20258.tabulate (22413-1) 256) source108.plan.table+
      4*22413*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*242091989018 := by decide +kernel
private theorem range64From21517To4033 : Segment 64 21517 22413 3584 4033 :=
  paid (pc:=59) (v:=242091989018) (by decide) source108_valid tests64_108_3584 fee64_108_22413 (by decide +kernel)

private theorem range64From21517 : Win 64 21517 22413 :=
  complete (by decide) (by decide) (join_population (join_population range64From21517To3509 range64From21517To3581) (join_population range64From21517To3584 range64From21517To4033))

private theorem fee64_114_23158 :
    PopulationFees20258.bill (n:=23158) (PopulationFees20258.tabulate (23158-1) 256) source114.plan.table+
      4*23158*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*224613640862 := by decide +kernel
private theorem range64From22414To3526 : Segment 64 22414 23158 0 3526 :=
  paid (pc:=67) (v:=224613640862) (by decide) source114_valid tests64_114_0 fee64_114_23158 (by decide +kernel)

private theorem tests64_114_3526 : ∀ z∈source114.plan.table,z.1.Valid 64 3526 := by decide +kernel
private theorem range64From22414To3581 : Segment 64 22414 23158 3526 3581 :=
  paid (pc:=67) (v:=224613640862) (by decide) source114_valid tests64_114_3526 fee64_114_23158 (by decide +kernel)

private theorem range64From22414To3584 : Segment 64 22414 23158 3581 3584 :=
  paid (pc:=67) (v:=224613640862) (by decide) source114_valid tests64_114_3581 fee64_114_23158 (by decide +kernel)

private theorem fee64_108_23158 :
    PopulationFees20258.bill (n:=23158) (PopulationFees20258.tabulate (23158-1) 256) source108.plan.table+
      4*23158*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*256997699194 := by decide +kernel
private theorem range64From22414To4033 : Segment 64 22414 23158 3584 4033 :=
  paid (pc:=62) (v:=256997699194) (by decide) source108_valid tests64_108_3584 fee64_108_23158 (by decide +kernel)

private theorem range64From22414 : Win 64 22414 23158 :=
  complete (by decide) (by decide) (join_population (join_population range64From22414To3526 range64From22414To3581) (join_population range64From22414To3584 range64From22414To4033))

private theorem fee64_114_23824 :
    PopulationFees20258.bill (n:=23824) (PopulationFees20258.tabulate (23824-1) 256) source114.plan.table+
      4*23824*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*236530105312 := by decide +kernel
private theorem range64From23159To3533 : Segment 64 23159 23824 0 3533 :=
  paid (pc:=69) (v:=236530105312) (by decide) source114_valid tests64_114_0 fee64_114_23824 (by decide +kernel)

private theorem tests64_114_3533 : ∀ z∈source114.plan.table,z.1.Valid 64 3533 := by decide +kernel
private theorem range64From23159To3584 : Segment 64 23159 23824 3533 3584 :=
  paid (pc:=68) (v:=236530105312) (by decide) source114_valid tests64_114_3533 fee64_114_23824 (by decide +kernel)

private theorem fee64_108_23824 :
    PopulationFees20258.bill (n:=23824) (PopulationFees20258.tabulate (23824-1) 256) source108.plan.table+
      4*23824*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*270571296730 := by decide +kernel
private theorem range64From23159To4033 : Segment 64 23159 23824 3584 4033 :=
  paid (pc:=64) (v:=270571296730) (by decide) source108_valid tests64_108_3584 fee64_108_23824 (by decide +kernel)

private theorem range64From23159 : Win 64 23159 23824 :=
  complete (by decide) (by decide) (join_population range64From23159To3533 (join_population range64From23159To3584 range64From23159To4033))

private theorem fee64_114_24450 :
    PopulationFees20258.bill (n:=24450) (PopulationFees20258.tabulate (24450-1) 256) source114.plan.table+
      4*24450*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*247926258632 := by decide +kernel
private theorem range64From23825To3540 : Segment 64 23825 24450 0 3540 :=
  paid (pc:=70) (v:=247926258632) (by decide) source114_valid tests64_114_0 fee64_114_24450 (by decide +kernel)

private theorem tests64_114_3540 : ∀ z∈source114.plan.table,z.1.Valid 64 3540 := by decide +kernel
private theorem range64From23825To3584 : Segment 64 23825 24450 3540 3584 :=
  paid (pc:=69) (v:=247926258632) (by decide) source114_valid tests64_114_3540 fee64_114_24450 (by decide +kernel)

private theorem fee64_108_24450 :
    PopulationFees20258.bill (n:=24450) (PopulationFees20258.tabulate (24450-1) 256) source108.plan.table+
      4*24450*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*283759782870 := by decide +kernel
private theorem range64From23825To4033 : Segment 64 23825 24450 3584 4033 :=
  paid (pc:=66) (v:=283759782870) (by decide) source108_valid tests64_108_3584 fee64_108_24450 (by decide +kernel)

private theorem range64From23825 : Win 64 23825 24450 :=
  complete (by decide) (by decide) (join_population range64From23825To3540 (join_population range64From23825To3584 range64From23825To4033))

private theorem fee64_114_25060 :
    PopulationFees20258.bill (n:=25060) (PopulationFees20258.tabulate (25060-1) 256) source114.plan.table+
      4*25060*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*259408046403 := by decide +kernel
private theorem range64From24451To3544 : Segment 64 24451 25060 0 3544 :=
  paid (pc:=70) (v:=259408046403) (by decide) source114_valid tests64_114_0 fee64_114_25060 (by decide +kernel)

private theorem tests64_114_3544 : ∀ z∈source114.plan.table,z.1.Valid 64 3544 := by decide +kernel
private theorem range64From24451To3584 : Segment 64 24451 25060 3544 3584 :=
  paid (pc:=70) (v:=259408046403) (by decide) source114_valid tests64_114_3544 fee64_114_25060 (by decide +kernel)

private theorem fee64_108_25060 :
    PopulationFees20258.bill (n:=25060) (PopulationFees20258.tabulate (25060-1) 256) source108.plan.table+
      4*25060*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*296999529794 := by decide +kernel
private theorem range64From24451To3971 : Segment 64 24451 25060 3584 3971 :=
  paid (pc:=67) (v:=296999529794) (by decide) source108_valid tests64_108_3584 fee64_108_25060 (by decide +kernel)

private theorem tests64_112_3971 : ∀ z∈source112.plan.table,z.1.Valid 64 3971 := by decide +kernel
private theorem fee64_112_25060 :
    PopulationFees20258.bill (n:=25060) (PopulationFees20258.tabulate (25060-1) 256) source112.plan.table+
      4*25060*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*310494233477 := by decide +kernel
private theorem range64From24451To4033 : Segment 64 24451 25060 3971 4033 :=
  paid (pc:=65) (v:=310494233477) (by decide) source112_valid tests64_112_3971 fee64_112_25060 (by decide +kernel)

private theorem range64From24451 : Win 64 24451 25060 :=
  complete (by decide) (by decide) (join_population (join_population range64From24451To3544 range64From24451To3584) (join_population range64From24451To3971 range64From24451To4033))

theorem cut64From20258 : Win 64 20258 25060 :=
  (join_ground (join_ground range64From20258 (join_ground range64From21517 range64From22414)) (join_ground range64From23159 (join_ground range64From23825 range64From24451)))

end JSP233.FiniteCutRanges20258
