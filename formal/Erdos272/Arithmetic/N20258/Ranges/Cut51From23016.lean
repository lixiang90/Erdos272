module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source036
public import Erdos272.Arithmetic.N20258.Sources.Source039
public import Erdos272.Arithmetic.N20258.Sources.Source042
public import Erdos272.Arithmetic.N20258.Sources.Source043
public import Erdos272.Arithmetic.N20258.Sources.Source045
public import Erdos272.Arithmetic.N20258.Sources.Source046

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests51_036_0 : ∀ z∈source036.plan.table,z.1.Valid 51 0 := by decide +kernel
private theorem fee51_036_23715 :
    PopulationFees20258.bill (n:=23715) (PopulationFees20258.tabulate (23715-1) 256) source036.plan.table+
      4*23715*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*159796790849 := by decide +kernel
private theorem range51From23016To2294 : Segment 51 23016 23715 0 2294 :=
  paid (pc:=78) (v:=159796790849) (by decide) source036_valid tests51_036_0 fee51_036_23715 (by decide +kernel)

private theorem tests51_039_2294 : ∀ z∈source039.plan.table,z.1.Valid 51 2294 := by decide +kernel
private theorem fee51_039_23715 :
    PopulationFees20258.bill (n:=23715) (PopulationFees20258.tabulate (23715-1) 256) source039.plan.table+
      4*23715*NaturalPopulation20258.weights source039.extras≤source039.plan.scale*184612456724 := by decide +kernel
private theorem range51From23016To2404 : Segment 51 23016 23715 2294 2404 :=
  paid (pc:=77) (v:=184612456724) (by decide) source039_valid tests51_039_2294 fee51_039_23715 (by decide +kernel)

private theorem tests51_043_2404 : ∀ z∈source043.plan.table,z.1.Valid 51 2404 := by decide +kernel
private theorem fee51_043_23715 :
    PopulationFees20258.bill (n:=23715) (PopulationFees20258.tabulate (23715-1) 256) source043.plan.table+
      4*23715*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*227355422757 := by decide +kernel
private theorem range51From23016To2462 : Segment 51 23016 23715 2404 2462 :=
  paid (pc:=77) (v:=227355422757) (by decide) source043_valid tests51_043_2404 fee51_043_23715 (by decide +kernel)

private theorem tests51_045_2462 : ∀ z∈source045.plan.table,z.1.Valid 51 2462 := by decide +kernel
private theorem fee51_045_23715 :
    PopulationFees20258.bill (n:=23715) (PopulationFees20258.tabulate (23715-1) 256) source045.plan.table+
      4*23715*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*276054560324 := by decide +kernel
private theorem range51From23016To2502 : Segment 51 23016 23715 2462 2502 :=
  paid (pc:=77) (v:=276054560324) (by decide) source045_valid tests51_045_2462 fee51_045_23715 (by decide +kernel)

private theorem tests51_045_2502 : ∀ z∈source045.plan.table,z.1.Valid 51 2502 := by decide +kernel
private theorem range51From23016To2503 : Segment 51 23016 23715 2502 2503 :=
  paid (pc:=77) (v:=276054560324) (by decide) source045_valid tests51_045_2502 fee51_045_23715 (by decide +kernel)

private theorem tests51_046_2503 : ∀ z∈source046.plan.table,z.1.Valid 51 2503 := by decide +kernel
private theorem fee51_046_23715 :
    PopulationFees20258.bill (n:=23715) (PopulationFees20258.tabulate (23715-1) 256) source046.plan.table+
      4*23715*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*260535935990 := by decide +kernel
private theorem range51From23016To2551 : Segment 51 23016 23715 2503 2551 :=
  paid (pc:=76) (v:=260535935990) (by decide) source046_valid tests51_046_2503 fee51_046_23715 (by decide +kernel)

private theorem range51From23016 : Win 51 23016 23715 :=
  complete (by decide) (by decide) (join_population (join_population range51From23016To2294 (join_population range51From23016To2404 range51From23016To2462)) (join_population range51From23016To2502 (join_population range51From23016To2503 range51From23016To2551)))

private theorem fee51_036_24562 :
    PopulationFees20258.bill (n:=24562) (PopulationFees20258.tabulate (24562-1) 256) source036.plan.table+
      4*24562*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*170596638977 := by decide +kernel
private theorem range51From23716To2316 : Segment 51 23716 24562 0 2316 :=
  paid (pc:=78) (v:=170596638977) (by decide) source036_valid tests51_036_0 fee51_036_24562 (by decide +kernel)

private theorem tests51_039_2316 : ∀ z∈source039.plan.table,z.1.Valid 51 2316 := by decide +kernel
private theorem fee51_039_24562 :
    PopulationFees20258.bill (n:=24562) (PopulationFees20258.tabulate (24562-1) 256) source039.plan.table+
      4*24562*NaturalPopulation20258.weights source039.extras≤source039.plan.scale*197083276090 := by decide +kernel
private theorem range51From23716To2420 : Segment 51 23716 24562 2316 2420 :=
  paid (pc:=77) (v:=197083276090) (by decide) source039_valid tests51_039_2316 fee51_039_24562 (by decide +kernel)

private theorem tests51_043_2420 : ∀ z∈source043.plan.table,z.1.Valid 51 2420 := by decide +kernel
private theorem fee51_043_24562 :
    PopulationFees20258.bill (n:=24562) (PopulationFees20258.tabulate (24562-1) 256) source043.plan.table+
      4*24562*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*242654746536 := by decide +kernel
private theorem range51From23716To2469 : Segment 51 23716 24562 2420 2469 :=
  paid (pc:=77) (v:=242654746536) (by decide) source043_valid tests51_043_2420 fee51_043_24562 (by decide +kernel)

private theorem tests51_045_2469 : ∀ z∈source045.plan.table,z.1.Valid 51 2469 := by decide +kernel
private theorem fee51_045_24562 :
    PopulationFees20258.bill (n:=24562) (PopulationFees20258.tabulate (24562-1) 256) source045.plan.table+
      4*24562*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*294525119371 := by decide +kernel
private theorem range51From23716To2501 : Segment 51 23716 24562 2469 2501 :=
  paid (pc:=77) (v:=294525119371) (by decide) source045_valid tests51_045_2469 fee51_045_24562 (by decide +kernel)

private theorem tests51_045_2501 : ∀ z∈source045.plan.table,z.1.Valid 51 2501 := by decide +kernel
private theorem range51From23716To2503 : Segment 51 23716 24562 2501 2503 :=
  paid (pc:=77) (v:=294525119371) (by decide) source045_valid tests51_045_2501 fee51_045_24562 (by decide +kernel)

private theorem fee51_046_24562 :
    PopulationFees20258.bill (n:=24562) (PopulationFees20258.tabulate (24562-1) 256) source046.plan.table+
      4*24562*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*278040339068 := by decide +kernel
private theorem range51From23716To2551 : Segment 51 23716 24562 2503 2551 :=
  paid (pc:=76) (v:=278040339068) (by decide) source046_valid tests51_046_2503 fee51_046_24562 (by decide +kernel)

private theorem range51From23716 : Win 51 23716 24562 :=
  complete (by decide) (by decide) (join_population (join_population range51From23716To2316 (join_population range51From23716To2420 range51From23716To2469)) (join_population range51From23716To2501 (join_population range51From23716To2503 range51From23716To2551)))

private theorem fee51_036_25604 :
    PopulationFees20258.bill (n:=25604) (PopulationFees20258.tabulate (25604-1) 256) source036.plan.table+
      4*25604*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*184251984531 := by decide +kernel
private theorem range51From24563To2340 : Segment 51 24563 25604 0 2340 :=
  paid (pc:=78) (v:=184251984531) (by decide) source036_valid tests51_036_0 fee51_036_25604 (by decide +kernel)

private theorem tests51_039_2340 : ∀ z∈source039.plan.table,z.1.Valid 51 2340 := by decide +kernel
private theorem fee51_039_25604 :
    PopulationFees20258.bill (n:=25604) (PopulationFees20258.tabulate (25604-1) 256) source039.plan.table+
      4*25604*NaturalPopulation20258.weights source039.extras≤source039.plan.scale*212864065482 := by decide +kernel
private theorem range51From24563To2435 : Segment 51 24563 25604 2340 2435 :=
  paid (pc:=77) (v:=212864065482) (by decide) source039_valid tests51_039_2340 fee51_039_25604 (by decide +kernel)

private theorem tests51_043_2435 : ∀ z∈source043.plan.table,z.1.Valid 51 2435 := by decide +kernel
private theorem fee51_043_25604 :
    PopulationFees20258.bill (n:=25604) (PopulationFees20258.tabulate (25604-1) 256) source043.plan.table+
      4*25604*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*262014471443 := by decide +kernel
private theorem range51From24563To2477 : Segment 51 24563 25604 2435 2477 :=
  paid (pc:=77) (v:=262014471443) (by decide) source043_valid tests51_043_2435 fee51_043_25604 (by decide +kernel)

private theorem tests51_045_2477 : ∀ z∈source045.plan.table,z.1.Valid 51 2477 := by decide +kernel
private theorem fee51_045_25604 :
    PopulationFees20258.bill (n:=25604) (PopulationFees20258.tabulate (25604-1) 256) source045.plan.table+
      4*25604*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*317936954985 := by decide +kernel
private theorem range51From24563To2501 : Segment 51 24563 25604 2477 2501 :=
  paid (pc:=76) (v:=317936954985) (by decide) source045_valid tests51_045_2477 fee51_045_25604 (by decide +kernel)

private theorem range51From24563To2503 : Segment 51 24563 25604 2501 2503 :=
  paid (pc:=76) (v:=317936954985) (by decide) source045_valid tests51_045_2501 fee51_045_25604 (by decide +kernel)

private theorem fee51_046_25604 :
    PopulationFees20258.bill (n:=25604) (PopulationFees20258.tabulate (25604-1) 256) source046.plan.table+
      4*25604*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*300168110934 := by decide +kernel
private theorem range51From24563To2551 : Segment 51 24563 25604 2503 2551 :=
  paid (pc:=76) (v:=300168110934) (by decide) source046_valid tests51_046_2503 fee51_046_25604 (by decide +kernel)

private theorem range51From24563 : Win 51 24563 25604 :=
  complete (by decide) (by decide) (join_population (join_population range51From24563To2340 (join_population range51From24563To2435 range51From24563To2477)) (join_population range51From24563To2501 (join_population range51From24563To2503 range51From24563To2551)))

private theorem fee51_036_26908 :
    PopulationFees20258.bill (n:=26908) (PopulationFees20258.tabulate (26908-1) 256) source036.plan.table+
      4*26908*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*202208164019 := by decide +kernel
private theorem range51From25605To2367 : Segment 51 25605 26908 0 2367 :=
  paid (pc:=77) (v:=202208164019) (by decide) source036_valid tests51_036_0 fee51_036_26908 (by decide +kernel)

private theorem tests51_042_2367 : ∀ z∈source042.plan.table,z.1.Valid 51 2367 := by decide +kernel
private theorem fee51_042_26908 :
    PopulationFees20258.bill (n:=26908) (PopulationFees20258.tabulate (26908-1) 256) source042.plan.table+
      4*26908*NaturalPopulation20258.weights source042.extras≤source042.plan.scale*294322973651 := by decide +kernel
private theorem range51From25605To2465 : Segment 51 25605 26908 2367 2465 :=
  paid (pc:=77) (v:=294322973651) (by decide) source042_valid tests51_042_2367 fee51_042_26908 (by decide +kernel)

private theorem tests51_045_2465 : ∀ z∈source045.plan.table,z.1.Valid 51 2465 := by decide +kernel
private theorem fee51_045_26908 :
    PopulationFees20258.bill (n:=26908) (PopulationFees20258.tabulate (26908-1) 256) source045.plan.table+
      4*26908*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*348660847976 := by decide +kernel
private theorem range51From25605To2502 : Segment 51 25605 26908 2465 2502 :=
  paid (pc:=76) (v:=348660847976) (by decide) source045_valid tests51_045_2465 fee51_045_26908 (by decide +kernel)

private theorem range51From25605To2503 : Segment 51 25605 26908 2502 2503 :=
  paid (pc:=76) (v:=348660847976) (by decide) source045_valid tests51_045_2502 fee51_045_26908 (by decide +kernel)

private theorem fee51_046_26908 :
    PopulationFees20258.bill (n:=26908) (PopulationFees20258.tabulate (26908-1) 256) source046.plan.table+
      4*26908*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*329264938761 := by decide +kernel
private theorem range51From25605To2551 : Segment 51 25605 26908 2503 2551 :=
  paid (pc:=76) (v:=329264938761) (by decide) source046_valid tests51_046_2503 fee51_046_26908 (by decide +kernel)

private theorem range51From25605 : Win 51 25605 26908 :=
  complete (by decide) (by decide) (join_population (join_population range51From25605To2367 range51From25605To2465) (join_population range51From25605To2502 (join_population range51From25605To2503 range51From25605To2551)))

theorem cut51From23016 : Win 51 23016 26908 :=
  (join_ground (join_ground range51From23016 range51From23716) (join_ground range51From24563 range51From25605))

end JSP233.FiniteCutRanges20258
