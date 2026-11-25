module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source101
public import Erdos272.Arithmetic.N20258.Sources.Source102

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests59_101_0 : ∀ z∈source101.plan.table,z.1.Valid 59 0 := by decide +kernel
private theorem fee59_101_25832 :
    PopulationFees20258.bill (n:=25832) (PopulationFees20258.tabulate (25832-1) 256) source101.plan.table+
      4*25832*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*252146513756 := by decide +kernel
private theorem range59From25414To3031 : Segment 59 25414 25832 0 3031 :=
  paid (pc:=76) (v:=252146513756) (by decide) source101_valid tests59_101_0 fee59_101_25832 (by decide +kernel)

private theorem tests59_102_3031 : ∀ z∈source102.plan.table,z.1.Valid 59 3031 := by decide +kernel
private theorem fee59_102_25832 :
    PopulationFees20258.bill (n:=25832) (PopulationFees20258.tabulate (25832-1) 256) source102.plan.table+
      4*25832*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*340437474654 := by decide +kernel
private theorem range59From25414To3354 : Segment 59 25414 25832 3031 3354 :=
  paid (pc:=74) (v:=340437474654) (by decide) source102_valid tests59_102_3031 fee59_102_25832 (by decide +kernel)

private theorem tests59_096_3354 : ∀ z∈source096.plan.table,z.1.Valid 59 3354 := by decide +kernel
private theorem fee59_096_25832 :
    PopulationFees20258.bill (n:=25832) (PopulationFees20258.tabulate (25832-1) 256) source096.plan.table+
      4*25832*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*328075390764 := by decide +kernel
private theorem range59From25414To3421 : Segment 59 25414 25832 3354 3421 :=
  paid (pc:=74) (v:=328075390764) (by decide) source096_valid tests59_096_3354 fee59_096_25832 (by decide +kernel)

private theorem tests59_096_3421 : ∀ z∈source096.plan.table,z.1.Valid 59 3421 := by decide +kernel
private theorem range59From25414To3423 : Segment 59 25414 25832 3421 3423 :=
  paid (pc:=73) (v:=328075390764) (by decide) source096_valid tests59_096_3421 fee59_096_25832 (by decide +kernel)

private theorem range59From25414 : Win 59 25414 25832 :=
  complete (by decide) (by decide) (join_population (join_population range59From25414To3031 range59From25414To3354) (join_population range59From25414To3421 range59From25414To3423))

private theorem fee59_101_26283 :
    PopulationFees20258.bill (n:=26283) (PopulationFees20258.tabulate (26283-1) 256) source101.plan.table+
      4*26283*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*260324293338 := by decide +kernel
private theorem range59From25833To3050 : Segment 59 25833 26283 0 3050 :=
  paid (pc:=76) (v:=260324293338) (by decide) source101_valid tests59_101_0 fee59_101_26283 (by decide +kernel)

private theorem tests59_102_3050 : ∀ z∈source102.plan.table,z.1.Valid 59 3050 := by decide +kernel
private theorem fee59_102_26283 :
    PopulationFees20258.bill (n:=26283) (PopulationFees20258.tabulate (26283-1) 256) source102.plan.table+
      4*26283*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*351400493696 := by decide +kernel
private theorem range59From25833To3357 : Segment 59 25833 26283 3050 3357 :=
  paid (pc:=74) (v:=351400493696) (by decide) source102_valid tests59_102_3050 fee59_102_26283 (by decide +kernel)

private theorem tests59_096_3357 : ∀ z∈source096.plan.table,z.1.Valid 59 3357 := by decide +kernel
private theorem fee59_096_26283 :
    PopulationFees20258.bill (n:=26283) (PopulationFees20258.tabulate (26283-1) 256) source096.plan.table+
      4*26283*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*338782735787 := by decide +kernel
private theorem range59From25833To3421 : Segment 59 25833 26283 3357 3421 :=
  paid (pc:=74) (v:=338782735787) (by decide) source096_valid tests59_096_3357 fee59_096_26283 (by decide +kernel)

private theorem range59From25833To3423 : Segment 59 25833 26283 3421 3423 :=
  paid (pc:=74) (v:=338782735787) (by decide) source096_valid tests59_096_3421 fee59_096_26283 (by decide +kernel)

private theorem range59From25833 : Win 59 25833 26283 :=
  complete (by decide) (by decide) (join_population (join_population range59From25833To3050 range59From25833To3357) (join_population range59From25833To3421 range59From25833To3423))

private theorem fee59_101_26776 :
    PopulationFees20258.bill (n:=26776) (PopulationFees20258.tabulate (26776-1) 256) source101.plan.table+
      4*26776*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*269345398028 := by decide +kernel
private theorem range59From26284To3068 : Segment 59 26284 26776 0 3068 :=
  paid (pc:=76) (v:=269345398028) (by decide) source101_valid tests59_101_0 fee59_101_26776 (by decide +kernel)

private theorem tests59_102_3068 : ∀ z∈source102.plan.table,z.1.Valid 59 3068 := by decide +kernel
private theorem fee59_102_26776 :
    PopulationFees20258.bill (n:=26776) (PopulationFees20258.tabulate (26776-1) 256) source102.plan.table+
      4*26776*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*363467081397 := by decide +kernel
private theorem range59From26284To3359 : Segment 59 26284 26776 3068 3359 :=
  paid (pc:=74) (v:=363467081397) (by decide) source102_valid tests59_102_3068 fee59_102_26776 (by decide +kernel)

private theorem tests59_096_3359 : ∀ z∈source096.plan.table,z.1.Valid 59 3359 := by decide +kernel
private theorem fee59_096_26776 :
    PopulationFees20258.bill (n:=26776) (PopulationFees20258.tabulate (26776-1) 256) source096.plan.table+
      4*26776*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*350567966119 := by decide +kernel
private theorem range59From26284To3421 : Segment 59 26284 26776 3359 3421 :=
  paid (pc:=74) (v:=350567966119) (by decide) source096_valid tests59_096_3359 fee59_096_26776 (by decide +kernel)

private theorem range59From26284To3423 : Segment 59 26284 26776 3421 3423 :=
  paid (pc:=74) (v:=350567966119) (by decide) source096_valid tests59_096_3421 fee59_096_26776 (by decide +kernel)

private theorem range59From26284 : Win 59 26284 26776 :=
  complete (by decide) (by decide) (join_population (join_population range59From26284To3068 range59From26284To3359) (join_population range59From26284To3421 range59From26284To3423))

private theorem fee59_101_27320 :
    PopulationFees20258.bill (n:=27320) (PopulationFees20258.tabulate (27320-1) 256) source101.plan.table+
      4*27320*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*279592319463 := by decide +kernel
private theorem range59From26777To3087 : Segment 59 26777 27320 0 3087 :=
  paid (pc:=76) (v:=279592319463) (by decide) source101_valid tests59_101_0 fee59_101_27320 (by decide +kernel)

private theorem tests59_102_3087 : ∀ z∈source102.plan.table,z.1.Valid 59 3087 := by decide +kernel
private theorem fee59_102_27320 :
    PopulationFees20258.bill (n:=27320) (PopulationFees20258.tabulate (27320-1) 256) source102.plan.table+
      4*27320*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*377193945472 := by decide +kernel
private theorem range59From26777To3364 : Segment 59 26777 27320 3087 3364 :=
  paid (pc:=75) (v:=377193945472) (by decide) source102_valid tests59_102_3087 fee59_102_27320 (by decide +kernel)

private theorem tests59_096_3364 : ∀ z∈source096.plan.table,z.1.Valid 59 3364 := by decide +kernel
private theorem fee59_096_27320 :
    PopulationFees20258.bill (n:=27320) (PopulationFees20258.tabulate (27320-1) 256) source096.plan.table+
      4*27320*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*363878046223 := by decide +kernel
private theorem range59From26777To3422 : Segment 59 26777 27320 3364 3422 :=
  paid (pc:=74) (v:=363878046223) (by decide) source096_valid tests59_096_3364 fee59_096_27320 (by decide +kernel)

private theorem tests59_096_3422 : ∀ z∈source096.plan.table,z.1.Valid 59 3422 := by decide +kernel
private theorem range59From26777To3423 : Segment 59 26777 27320 3422 3423 :=
  paid (pc:=74) (v:=363878046223) (by decide) source096_valid tests59_096_3422 fee59_096_27320 (by decide +kernel)

private theorem range59From26777 : Win 59 26777 27320 :=
  complete (by decide) (by decide) (join_population (join_population range59From26777To3087 range59From26777To3364) (join_population range59From26777To3422 range59From26777To3423))

private theorem fee59_101_27930 :
    PopulationFees20258.bill (n:=27930) (PopulationFees20258.tabulate (27930-1) 256) source101.plan.table+
      4*27930*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*291261243441 := by decide +kernel
private theorem range59From27321To3107 : Segment 59 27321 27930 0 3107 :=
  paid (pc:=77) (v:=291261243441) (by decide) source101_valid tests59_101_0 fee59_101_27930 (by decide +kernel)

private theorem tests59_102_3107 : ∀ z∈source102.plan.table,z.1.Valid 59 3107 := by decide +kernel
private theorem fee59_102_27930 :
    PopulationFees20258.bill (n:=27930) (PopulationFees20258.tabulate (27930-1) 256) source102.plan.table+
      4*27930*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*392827580807 := by decide +kernel
private theorem range59From27321To3366 : Segment 59 27321 27930 3107 3366 :=
  paid (pc:=75) (v:=392827580807) (by decide) source102_valid tests59_102_3107 fee59_102_27930 (by decide +kernel)

private theorem tests59_096_3366 : ∀ z∈source096.plan.table,z.1.Valid 59 3366 := by decide +kernel
private theorem fee59_096_27930 :
    PopulationFees20258.bill (n:=27930) (PopulationFees20258.tabulate (27930-1) 256) source096.plan.table+
      4*27930*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*379149079063 := by decide +kernel
private theorem range59From27321To3423 : Segment 59 27321 27930 3366 3423 :=
  paid (pc:=75) (v:=379149079063) (by decide) source096_valid tests59_096_3366 fee59_096_27930 (by decide +kernel)

private theorem range59From27321 : Win 59 27321 27930 :=
  complete (by decide) (by decide) (join_population range59From27321To3107 (join_population range59From27321To3366 range59From27321To3423))

private theorem fee59_101_28622 :
    PopulationFees20258.bill (n:=28622) (PopulationFees20258.tabulate (28622-1) 256) source101.plan.table+
      4*28622*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*305056115649 := by decide +kernel
private theorem range59From27931To3126 : Segment 59 27931 28622 0 3126 :=
  paid (pc:=77) (v:=305056115649) (by decide) source101_valid tests59_101_0 fee59_101_28622 (by decide +kernel)

private theorem tests59_102_3126 : ∀ z∈source102.plan.table,z.1.Valid 59 3126 := by decide +kernel
private theorem fee59_102_28622 :
    PopulationFees20258.bill (n:=28622) (PopulationFees20258.tabulate (28622-1) 256) source102.plan.table+
      4*28622*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*411245096009 := by decide +kernel
private theorem range59From27931To3368 : Segment 59 27931 28622 3126 3368 :=
  paid (pc:=75) (v:=411245096009) (by decide) source102_valid tests59_102_3126 fee59_102_28622 (by decide +kernel)

private theorem tests59_096_3368 : ∀ z∈source096.plan.table,z.1.Valid 59 3368 := by decide +kernel
private theorem fee59_096_28622 :
    PopulationFees20258.bill (n:=28622) (PopulationFees20258.tabulate (28622-1) 256) source096.plan.table+
      4*28622*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*396901368161 := by decide +kernel
private theorem range59From27931To3423 : Segment 59 27931 28622 3368 3423 :=
  paid (pc:=75) (v:=396901368161) (by decide) source096_valid tests59_096_3368 fee59_096_28622 (by decide +kernel)

private theorem range59From27931 : Win 59 27931 28622 :=
  complete (by decide) (by decide) (join_population range59From27931To3126 (join_population range59From27931To3368 range59From27931To3423))

theorem cut59From25414 : Win 59 25414 28622 :=
  (join_ground (join_ground range59From25414 (join_ground range59From25833 range59From26284)) (join_ground range59From26777 (join_ground range59From27321 range59From27931)))

end JSP233.FiniteCutRanges20258
