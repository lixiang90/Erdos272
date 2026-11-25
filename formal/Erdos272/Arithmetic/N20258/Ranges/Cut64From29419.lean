module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source109
public import Erdos272.Arithmetic.N20258.Sources.Source111
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source114

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests64_114_0 : ∀ z∈source114.plan.table,z.1.Valid 64 0 := by decide +kernel
private theorem fee64_114_30464 :
    PopulationFees20258.bill (n:=30464) (PopulationFees20258.tabulate (30464-1) 256) source114.plan.table+
      4*30464*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*371772022536 := by decide +kernel
private theorem range64From29419To3564 : Segment 64 29419 30464 0 3564 :=
  paid (pc:=74) (v:=371772022536) (by decide) source114_valid tests64_114_0 fee64_114_30464 (by decide +kernel)

private theorem tests64_114_3564 : ∀ z∈source114.plan.table,z.1.Valid 64 3564 := by decide +kernel
private theorem range64From29419To3584 : Segment 64 29419 30464 3564 3584 :=
  paid (pc:=74) (v:=371772022536) (by decide) source114_valid tests64_114_3564 fee64_114_30464 (by decide +kernel)

private theorem tests64_108_3584 : ∀ z∈source108.plan.table,z.1.Valid 64 3584 := by decide +kernel
private theorem fee64_108_30464 :
    PopulationFees20258.bill (n:=30464) (PopulationFees20258.tabulate (30464-1) 256) source108.plan.table+
      4*30464*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*426159717164 := by decide +kernel
private theorem range64From29419To3752 : Segment 64 29419 30464 3584 3752 :=
  paid (pc:=73) (v:=426159717164) (by decide) source108_valid tests64_108_3584 fee64_108_30464 (by decide +kernel)

private theorem tests64_111_3752 : ∀ z∈source111.plan.table,z.1.Valid 64 3752 := by decide +kernel
private theorem fee64_111_30464 :
    PopulationFees20258.bill (n:=30464) (PopulationFees20258.tabulate (30464-1) 256) source111.plan.table+
      4*30464*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*453287911933 := by decide +kernel
private theorem range64From29419To4033 : Segment 64 29419 30464 3752 4033 :=
  paid (pc:=71) (v:=453287911933) (by decide) source111_valid tests64_111_3752 fee64_111_30464 (by decide +kernel)

private theorem range64From29419 : Win 64 29419 30464 :=
  complete (by decide) (by decide) (join_population (join_population range64From29419To3564 range64From29419To3584) (join_population range64From29419To3752 range64From29419To4033))

private theorem fee64_114_31695 :
    PopulationFees20258.bill (n:=31695) (PopulationFees20258.tabulate (31695-1) 256) source114.plan.table+
      4*31695*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*400252504334 := by decide +kernel
private theorem range64From30465To3566 : Segment 64 30465 31695 0 3566 :=
  paid (pc:=74) (v:=400252504334) (by decide) source114_valid tests64_114_0 fee64_114_31695 (by decide +kernel)

private theorem tests64_114_3566 : ∀ z∈source114.plan.table,z.1.Valid 64 3566 := by decide +kernel
private theorem range64From30465To3584 : Segment 64 30465 31695 3566 3584 :=
  paid (pc:=74) (v:=400252504334) (by decide) source114_valid tests64_114_3566 fee64_114_31695 (by decide +kernel)

private theorem fee64_108_31695 :
    PopulationFees20258.bill (n:=31695) (PopulationFees20258.tabulate (31695-1) 256) source108.plan.table+
      4*31695*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*458744800453 := by decide +kernel
private theorem range64From30465To3732 : Segment 64 30465 31695 3584 3732 :=
  paid (pc:=73) (v:=458744800453) (by decide) source108_valid tests64_108_3584 fee64_108_31695 (by decide +kernel)

private theorem tests64_111_3732 : ∀ z∈source111.plan.table,z.1.Valid 64 3732 := by decide +kernel
private theorem fee64_111_31695 :
    PopulationFees20258.bill (n:=31695) (PopulationFees20258.tabulate (31695-1) 256) source111.plan.table+
      4*31695*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*488299980449 := by decide +kernel
private theorem range64From30465To4014 : Segment 64 30465 31695 3732 4014 :=
  paid (pc:=71) (v:=488299980449) (by decide) source111_valid tests64_111_3732 fee64_111_31695 (by decide +kernel)

private theorem tests64_112_4014 : ∀ z∈source112.plan.table,z.1.Valid 64 4014 := by decide +kernel
private theorem fee64_112_31695 :
    PopulationFees20258.bill (n:=31695) (PopulationFees20258.tabulate (31695-1) 256) source112.plan.table+
      4*31695*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*479707099432 := by decide +kernel
private theorem range64From30465To4033 : Segment 64 30465 31695 4014 4033 :=
  paid (pc:=71) (v:=479707099432) (by decide) source112_valid tests64_112_4014 fee64_112_31695 (by decide +kernel)

private theorem range64From30465 : Win 64 30465 31695 :=
  complete (by decide) (by decide) (join_population (join_population range64From30465To3566 range64From30465To3584) (join_population range64From30465To3732 (join_population range64From30465To4014 range64From30465To4033)))

private theorem fee64_114_33075 :
    PopulationFees20258.bill (n:=33075) (PopulationFees20258.tabulate (33075-1) 256) source114.plan.table+
      4*33075*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*433207773233 := by decide +kernel
private theorem range64From31696To3603 : Segment 64 31696 33075 0 3603 :=
  paid (pc:=74) (v:=433207773233) (by decide) source114_valid tests64_114_0 fee64_114_33075 (by decide +kernel)

private theorem tests64_109_3603 : ∀ z∈source109.plan.table,z.1.Valid 64 3603 := by decide +kernel
private theorem fee64_109_33075 :
    PopulationFees20258.bill (n:=33075) (PopulationFees20258.tabulate (33075-1) 256) source109.plan.table+
      4*33075*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*491933040051 := by decide +kernel
private theorem range64From31696To3763 : Segment 64 31696 33075 3603 3763 :=
  paid (pc:=73) (v:=491933040051) (by decide) source109_valid tests64_109_3603 fee64_109_33075 (by decide +kernel)

private theorem tests64_112_3763 : ∀ z∈source112.plan.table,z.1.Valid 64 3763 := by decide +kernel
private theorem fee64_112_33075 :
    PopulationFees20258.bill (n:=33075) (PopulationFees20258.tabulate (33075-1) 256) source112.plan.table+
      4*33075*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*519293537114 := by decide +kernel
private theorem range64From31696To4027 : Segment 64 31696 33075 3763 4027 :=
  paid (pc:=72) (v:=519293537114) (by decide) source112_valid tests64_112_3763 fee64_112_33075 (by decide +kernel)

private theorem tests64_112_4027 : ∀ z∈source112.plan.table,z.1.Valid 64 4027 := by decide +kernel
private theorem range64From31696To4033 : Segment 64 31696 33075 4027 4033 :=
  paid (pc:=72) (v:=519293537114) (by decide) source112_valid tests64_112_4027 fee64_112_33075 (by decide +kernel)

private theorem range64From31696 : Win 64 31696 33075 :=
  complete (by decide) (by decide) (join_population (join_population range64From31696To3603 range64From31696To3763) (join_population range64From31696To4027 range64From31696To4033))

private theorem fee64_114_34630 :
    PopulationFees20258.bill (n:=34630) (PopulationFees20258.tabulate (34630-1) 256) source114.plan.table+
      4*34630*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*471965727135 := by decide +kernel
private theorem range64From33076To3650 : Segment 64 33076 34630 0 3650 :=
  paid (pc:=74) (v:=471965727135) (by decide) source114_valid tests64_114_0 fee64_114_34630 (by decide +kernel)

private theorem tests64_109_3650 : ∀ z∈source109.plan.table,z.1.Valid 64 3650 := by decide +kernel
private theorem fee64_109_34630 :
    PopulationFees20258.bill (n:=34630) (PopulationFees20258.tabulate (34630-1) 256) source109.plan.table+
      4*34630*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*535904459805 := by decide +kernel
private theorem range64From33076To3792 : Segment 64 33076 34630 3650 3792 :=
  paid (pc:=74) (v:=535904459805) (by decide) source109_valid tests64_109_3650 fee64_109_34630 (by decide +kernel)

private theorem tests64_112_3792 : ∀ z∈source112.plan.table,z.1.Valid 64 3792 := by decide +kernel
private theorem fee64_112_34630 :
    PopulationFees20258.bill (n:=34630) (PopulationFees20258.tabulate (34630-1) 256) source112.plan.table+
      4*34630*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*566028034080 := by decide +kernel
private theorem range64From33076To4028 : Segment 64 33076 34630 3792 4028 :=
  paid (pc:=72) (v:=566028034080) (by decide) source112_valid tests64_112_3792 fee64_112_34630 (by decide +kernel)

private theorem tests64_112_4028 : ∀ z∈source112.plan.table,z.1.Valid 64 4028 := by decide +kernel
private theorem range64From33076To4033 : Segment 64 33076 34630 4028 4033 :=
  paid (pc:=72) (v:=566028034080) (by decide) source112_valid tests64_112_4028 fee64_112_34630 (by decide +kernel)

private theorem range64From33076 : Win 64 33076 34630 :=
  complete (by decide) (by decide) (join_population (join_population range64From33076To3650 range64From33076To3792) (join_population range64From33076To4028 range64From33076To4033))

private theorem fee64_114_36439 :
    PopulationFees20258.bill (n:=36439) (PopulationFees20258.tabulate (36439-1) 256) source114.plan.table+
      4*36439*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*519318786604 := by decide +kernel
private theorem range64From34631To3693 : Segment 64 34631 36439 0 3693 :=
  paid (pc:=75) (v:=519318786604) (by decide) source114_valid tests64_114_0 fee64_114_36439 (by decide +kernel)

private theorem tests64_109_3693 : ∀ z∈source109.plan.table,z.1.Valid 64 3693 := by decide +kernel
private theorem fee64_109_36439 :
    PopulationFees20258.bill (n:=36439) (PopulationFees20258.tabulate (36439-1) 256) source109.plan.table+
      4*36439*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*590001832677 := by decide +kernel
private theorem range64From34631To3818 : Segment 64 34631 36439 3693 3818 :=
  paid (pc:=74) (v:=590001832677) (by decide) source109_valid tests64_109_3693 fee64_109_36439 (by decide +kernel)

private theorem tests64_112_3818 : ∀ z∈source112.plan.table,z.1.Valid 64 3818 := by decide +kernel
private theorem fee64_112_36439 :
    PopulationFees20258.bill (n:=36439) (PopulationFees20258.tabulate (36439-1) 256) source112.plan.table+
      4*36439*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*622822649718 := by decide +kernel
private theorem range64From34631To4029 : Segment 64 34631 36439 3818 4029 :=
  paid (pc:=73) (v:=622822649718) (by decide) source112_valid tests64_112_3818 fee64_112_36439 (by decide +kernel)

private theorem tests64_112_4029 : ∀ z∈source112.plan.table,z.1.Valid 64 4029 := by decide +kernel
private theorem range64From34631To4033 : Segment 64 34631 36439 4029 4033 :=
  paid (pc:=73) (v:=622822649718) (by decide) source112_valid tests64_112_4029 fee64_112_36439 (by decide +kernel)

private theorem range64From34631 : Win 64 34631 36439 :=
  complete (by decide) (by decide) (join_population (join_population range64From34631To3693 range64From34631To3818) (join_population range64From34631To4029 range64From34631To4033))

private theorem fee64_114_38608 :
    PopulationFees20258.bill (n:=38608) (PopulationFees20258.tabulate (38608-1) 256) source114.plan.table+
      4*38608*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*578650783217 := by decide +kernel
private theorem range64From36440To3735 : Segment 64 36440 38608 0 3735 :=
  paid (pc:=74) (v:=578650783217) (by decide) source114_valid tests64_114_0 fee64_114_38608 (by decide +kernel)

private theorem tests64_111_3735 : ∀ z∈source111.plan.table,z.1.Valid 64 3735 := by decide +kernel
private theorem fee64_111_38608 :
    PopulationFees20258.bill (n:=38608) (PopulationFees20258.tabulate (38608-1) 256) source111.plan.table+
      4*38608*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*706342767657 := by decide +kernel
private theorem range64From36440To4007 : Segment 64 36440 38608 3735 4007 :=
  paid (pc:=73) (v:=706342767657) (by decide) source111_valid tests64_111_3735 fee64_111_38608 (by decide +kernel)

private theorem tests64_112_4007 : ∀ z∈source112.plan.table,z.1.Valid 64 4007 := by decide +kernel
private theorem fee64_112_38608 :
    PopulationFees20258.bill (n:=38608) (PopulationFees20258.tabulate (38608-1) 256) source112.plan.table+
      4*38608*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*694209954088 := by decide +kernel
private theorem range64From36440To4033 : Segment 64 36440 38608 4007 4033 :=
  paid (pc:=73) (v:=694209954088) (by decide) source112_valid tests64_112_4007 fee64_112_38608 (by decide +kernel)

private theorem range64From36440 : Win 64 36440 38608 :=
  complete (by decide) (by decide) (join_population range64From36440To3735 (join_population range64From36440To4007 range64From36440To4033))

theorem cut64From29419 : Win 64 29419 38608 :=
  (join_ground (join_ground range64From29419 (join_ground range64From30465 range64From31696)) (join_ground range64From33076 (join_ground range64From34631 range64From36440)))

end JSP233.FiniteCutRanges20258
