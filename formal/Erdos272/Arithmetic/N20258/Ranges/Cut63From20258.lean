module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source113

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests63_113_0 : ∀ z∈source113.plan.table,z.1.Valid 63 0 := by decide +kernel
private theorem fee63_113_21518 :
    PopulationFees20258.bill (n:=21518) (PopulationFees20258.tabulate (21518-1) 256) source113.plan.table+
      4*21518*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*212862776590 := by decide +kernel
private theorem range63From20258To3158 : Segment 63 20258 21518 0 3158 :=
  paid (pc:=64) (v:=212862776590) (by decide) source113_valid tests63_113_0 fee63_113_21518 (by decide +kernel)

private theorem tests63_113_3158 : ∀ z∈source113.plan.table,z.1.Valid 63 3158 := by decide +kernel
private theorem range63From20258To3232 : Segment 63 20258 21518 3158 3232 :=
  paid (pc:=64) (v:=212862776590) (by decide) source113_valid tests63_113_3158 fee63_113_21518 (by decide +kernel)

private theorem tests63_105_3232 : ∀ z∈source105.plan.table,z.1.Valid 63 3232 := by decide +kernel
private theorem fee63_105_21518 :
    PopulationFees20258.bill (n:=21518) (PopulationFees20258.tabulate (21518-1) 256) source105.plan.table+
      4*21518*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*273524339594 := by decide +kernel
private theorem range63From20258To3501 : Segment 63 20258 21518 3232 3501 :=
  paid (pc:=61) (v:=273524339594) (by decide) source105_valid tests63_105_3232 fee63_105_21518 (by decide +kernel)

private theorem tests63_105_3501 : ∀ z∈source105.plan.table,z.1.Valid 63 3501 := by decide +kernel
private theorem range63From20258To3532 : Segment 63 20258 21518 3501 3532 :=
  paid (pc:=60) (v:=273524339594) (by decide) source105_valid tests63_105_3501 fee63_105_21518 (by decide +kernel)

private theorem tests63_108_3532 : ∀ z∈source108.plan.table,z.1.Valid 63 3532 := by decide +kernel
private theorem fee63_108_21518 :
    PopulationFees20258.bill (n:=21518) (PopulationFees20258.tabulate (21518-1) 256) source108.plan.table+
      4*21518*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*224747565571 := by decide +kernel
private theorem range63From20258To3907 : Segment 63 20258 21518 3532 3907 :=
  paid (pc:=55) (v:=224747565571) (by decide) source108_valid tests63_108_3532 fee63_108_21518 (by decide +kernel)

private theorem range63From20258 : Win 63 20258 21518 :=
  complete (by decide) (by decide) (join_population (join_population range63From20258To3158 range63From20258To3232) (join_population range63From20258To3501 (join_population range63From20258To3532 range63From20258To3907)))

private theorem fee63_113_22410 :
    PopulationFees20258.bill (n:=22410) (PopulationFees20258.tabulate (22410-1) 256) source113.plan.table+
      4*22410*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*229162914083 := by decide +kernel
private theorem range63From21519To3311 : Segment 63 21519 22410 0 3311 :=
  paid (pc:=67) (v:=229162914083) (by decide) source113_valid tests63_113_0 fee63_113_22410 (by decide +kernel)

private theorem tests63_105_3311 : ∀ z∈source105.plan.table,z.1.Valid 63 3311 := by decide +kernel
private theorem fee63_105_22410 :
    PopulationFees20258.bill (n:=22410) (PopulationFees20258.tabulate (22410-1) 256) source105.plan.table+
      4*22410*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*294259715829 := by decide +kernel
private theorem range63From21519To3518 : Segment 63 21519 22410 3311 3518 :=
  paid (pc:=65) (v:=294259715829) (by decide) source105_valid tests63_105_3311 fee63_105_22410 (by decide +kernel)

private theorem tests63_105_3518 : ∀ z∈source105.plan.table,z.1.Valid 63 3518 := by decide +kernel
private theorem range63From21519To3529 : Segment 63 21519 22410 3518 3529 :=
  paid (pc:=65) (v:=294259715829) (by decide) source105_valid tests63_105_3518 fee63_105_22410 (by decide +kernel)

private theorem tests63_108_3529 : ∀ z∈source108.plan.table,z.1.Valid 63 3529 := by decide +kernel
private theorem fee63_108_22410 :
    PopulationFees20258.bill (n:=22410) (PopulationFees20258.tabulate (22410-1) 256) source108.plan.table+
      4*22410*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*242025560965 := by decide +kernel
private theorem range63From21519To3907 : Segment 63 21519 22410 3529 3907 :=
  paid (pc:=60) (v:=242025560965) (by decide) source108_valid tests63_108_3529 fee63_108_22410 (by decide +kernel)

private theorem range63From21519 : Win 63 21519 22410 :=
  complete (by decide) (by decide) (join_population (join_population range63From21519To3311 range63From21519To3518) (join_population range63From21519To3529 range63From21519To3907))

private theorem fee63_113_23136 :
    PopulationFees20258.bill (n:=23136) (PopulationFees20258.tabulate (23136-1) 256) source113.plan.table+
      4*23136*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*242845171600 := by decide +kernel
private theorem range63From22411To3369 : Segment 63 22411 23136 0 3369 :=
  paid (pc:=69) (v:=242845171600) (by decide) source113_valid tests63_113_0 fee63_113_23136 (by decide +kernel)

private theorem tests63_105_3369 : ∀ z∈source105.plan.table,z.1.Valid 63 3369 := by decide +kernel
private theorem fee63_105_23136 :
    PopulationFees20258.bill (n:=23136) (PopulationFees20258.tabulate (23136-1) 256) source105.plan.table+
      4*23136*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*311665818256 := by decide +kernel
private theorem range63From22411To3524 : Segment 63 22411 23136 3369 3524 :=
  paid (pc:=67) (v:=311665818256) (by decide) source105_valid tests63_105_3369 fee63_105_23136 (by decide +kernel)

private theorem tests63_105_3524 : ∀ z∈source105.plan.table,z.1.Valid 63 3524 := by decide +kernel
private theorem range63From22411To3530 : Segment 63 22411 23136 3524 3530 :=
  paid (pc:=67) (v:=311665818256) (by decide) source105_valid tests63_105_3524 fee63_105_23136 (by decide +kernel)

private theorem tests63_108_3530 : ∀ z∈source108.plan.table,z.1.Valid 63 3530 := by decide +kernel
private theorem fee63_108_23136 :
    PopulationFees20258.bill (n:=23136) (PopulationFees20258.tabulate (23136-1) 256) source108.plan.table+
      4*23136*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*256526907011 := by decide +kernel
private theorem range63From22411To3907 : Segment 63 22411 23136 3530 3907 :=
  paid (pc:=63) (v:=256526907011) (by decide) source108_valid tests63_108_3530 fee63_108_23136 (by decide +kernel)

private theorem range63From22411 : Win 63 22411 23136 :=
  complete (by decide) (by decide) (join_population (join_population range63From22411To3369 range63From22411To3524) (join_population range63From22411To3530 range63From22411To3907))

private theorem fee63_113_23776 :
    PopulationFees20258.bill (n:=23776) (PopulationFees20258.tabulate (23776-1) 256) source113.plan.table+
      4*23776*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*255017874765 := by decide +kernel
private theorem range63From23137To3402 : Segment 63 23137 23776 0 3402 :=
  paid (pc:=70) (v:=255017874765) (by decide) source113_valid tests63_113_0 fee63_113_23776 (by decide +kernel)

private theorem tests63_105_3402 : ∀ z∈source105.plan.table,z.1.Valid 63 3402 := by decide +kernel
private theorem fee63_105_23776 :
    PopulationFees20258.bill (n:=23776) (PopulationFees20258.tabulate (23776-1) 256) source105.plan.table+
      4*23776*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*327362227889 := by decide +kernel
private theorem range63From23137To3524 : Segment 63 23137 23776 3402 3524 :=
  paid (pc:=69) (v:=327362227889) (by decide) source105_valid tests63_105_3402 fee63_105_23776 (by decide +kernel)

private theorem range63From23137To3529 : Segment 63 23137 23776 3524 3529 :=
  paid (pc:=69) (v:=327362227889) (by decide) source105_valid tests63_105_3524 fee63_105_23776 (by decide +kernel)

private theorem fee63_108_23776 :
    PopulationFees20258.bill (n:=23776) (PopulationFees20258.tabulate (23776-1) 256) source108.plan.table+
      4*23776*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*269693062147 := by decide +kernel
private theorem range63From23137To3907 : Segment 63 23137 23776 3529 3907 :=
  paid (pc:=65) (v:=269693062147) (by decide) source108_valid tests63_108_3529 fee63_108_23776 (by decide +kernel)

private theorem range63From23137 : Win 63 23137 23776 :=
  complete (by decide) (by decide) (join_population (join_population range63From23137To3402 range63From23137To3524) (join_population range63From23137To3529 range63From23137To3907))

private theorem fee63_113_24363 :
    PopulationFees20258.bill (n:=24363) (PopulationFees20258.tabulate (24363-1) 256) source113.plan.table+
      4*24363*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*266694681733 := by decide +kernel
private theorem range63From23777To3426 : Segment 63 23777 24363 0 3426 :=
  paid (pc:=71) (v:=266694681733) (by decide) source113_valid tests63_113_0 fee63_113_24363 (by decide +kernel)

private theorem tests63_105_3426 : ∀ z∈source105.plan.table,z.1.Valid 63 3426 := by decide +kernel
private theorem fee63_105_24363 :
    PopulationFees20258.bill (n:=24363) (PopulationFees20258.tabulate (24363-1) 256) source105.plan.table+
      4*24363*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*342291464084 := by decide +kernel
private theorem range63From23777To3527 : Segment 63 23777 24363 3426 3527 :=
  paid (pc:=70) (v:=342291464084) (by decide) source105_valid tests63_105_3426 fee63_105_24363 (by decide +kernel)

private theorem tests63_105_3527 : ∀ z∈source105.plan.table,z.1.Valid 63 3527 := by decide +kernel
private theorem range63From23777To3529 : Segment 63 23777 24363 3527 3529 :=
  paid (pc:=70) (v:=342291464084) (by decide) source105_valid tests63_105_3527 fee63_105_24363 (by decide +kernel)

private theorem fee63_108_24363 :
    PopulationFees20258.bill (n:=24363) (PopulationFees20258.tabulate (24363-1) 256) source108.plan.table+
      4*24363*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*282012146737 := by decide +kernel
private theorem range63From23777To3907 : Segment 63 23777 24363 3529 3907 :=
  paid (pc:=66) (v:=282012146737) (by decide) source108_valid tests63_108_3529 fee63_108_24363 (by decide +kernel)

private theorem range63From23777 : Win 63 23777 24363 :=
  complete (by decide) (by decide) (join_population (join_population range63From23777To3426 range63From23777To3527) (join_population range63From23777To3529 range63From23777To3907))

theorem cut63From20258 : Win 63 20258 24363 :=
  (join_ground (join_ground range63From20258 range63From21519) (join_ground range63From22411 (join_ground range63From23137 range63From23777)))

end JSP233.FiniteCutRanges20258
