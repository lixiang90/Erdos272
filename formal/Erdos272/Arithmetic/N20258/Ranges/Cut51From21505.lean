module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source036
public import Erdos272.Arithmetic.N20258.Sources.Source038
public import Erdos272.Arithmetic.N20258.Sources.Source041
public import Erdos272.Arithmetic.N20258.Sources.Source042
public import Erdos272.Arithmetic.N20258.Sources.Source043
public import Erdos272.Arithmetic.N20258.Sources.Source044
public import Erdos272.Arithmetic.N20258.Sources.Source045
public import Erdos272.Arithmetic.N20258.Sources.Source046

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests51_036_0 : ∀ z∈source036.plan.table,z.1.Valid 51 0 := by decide +kernel
private theorem fee51_036_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source036.plan.table+
      4*21931*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*138323288917 := by decide +kernel
private theorem range51From21505To2239 : Segment 51 21505 21931 0 2239 :=
  paid (pc:=79) (v:=138323288917) (by decide) source036_valid tests51_036_0 fee51_036_21931 (by decide +kernel)

private theorem tests51_038_2239 : ∀ z∈source038.plan.table,z.1.Valid 51 2239 := by decide +kernel
private theorem fee51_038_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source038.plan.table+
      4*21931*NaturalPopulation20258.weights source038.extras≤source038.plan.scale*165313419586 := by decide +kernel
private theorem range51From21505To2341 : Segment 51 21505 21931 2239 2341 :=
  paid (pc:=78) (v:=165313419586) (by decide) source038_valid tests51_038_2239 fee51_038_21931 (by decide +kernel)

private theorem tests51_041_2341 : ∀ z∈source041.plan.table,z.1.Valid 51 2341 := by decide +kernel
private theorem fee51_041_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source041.plan.table+
      4*21931*NaturalPopulation20258.weights source041.extras≤source041.plan.scale*207794728758 := by decide +kernel
private theorem range51From21505To2383 : Segment 51 21505 21931 2341 2383 :=
  paid (pc:=77) (v:=207794728758) (by decide) source041_valid tests51_041_2341 fee51_041_21931 (by decide +kernel)

private theorem tests51_043_2383 : ∀ z∈source043.plan.table,z.1.Valid 51 2383 := by decide +kernel
private theorem fee51_043_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source043.plan.table+
      4*21931*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*196916377685 := by decide +kernel
private theorem range51From21505To2440 : Segment 51 21505 21931 2383 2440 :=
  paid (pc:=77) (v:=196916377685) (by decide) source043_valid tests51_043_2383 fee51_043_21931 (by decide +kernel)

private theorem tests51_045_2440 : ∀ z∈source045.plan.table,z.1.Valid 51 2440 := by decide +kernel
private theorem fee51_045_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source045.plan.table+
      4*21931*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*239243018896 := by decide +kernel
private theorem range51From21505To2500 : Segment 51 21505 21931 2440 2500 :=
  paid (pc:=76) (v:=239243018896) (by decide) source045_valid tests51_045_2440 fee51_045_21931 (by decide +kernel)

private theorem tests51_045_2500 : ∀ z∈source045.plan.table,z.1.Valid 51 2500 := by decide +kernel
private theorem range51From21505To2501 : Segment 51 21505 21931 2500 2501 :=
  paid (pc:=76) (v:=239243018896) (by decide) source045_valid tests51_045_2500 fee51_045_21931 (by decide +kernel)

private theorem tests51_045_2501 : ∀ z∈source045.plan.table,z.1.Valid 51 2501 := by decide +kernel
private theorem range51From21505To2503 : Segment 51 21505 21931 2501 2503 :=
  paid (pc:=76) (v:=239243018896) (by decide) source045_valid tests51_045_2501 fee51_045_21931 (by decide +kernel)

private theorem tests51_046_2503 : ∀ z∈source046.plan.table,z.1.Valid 51 2503 := by decide +kernel
private theorem fee51_046_21931 :
    PopulationFees20258.bill (n:=21931) (PopulationFees20258.tabulate (21931-1) 256) source046.plan.table+
      4*21931*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*225716815580 := by decide +kernel
private theorem range51From21505To2551 : Segment 51 21505 21931 2503 2551 :=
  paid (pc:=76) (v:=225716815580) (by decide) source046_valid tests51_046_2503 fee51_046_21931 (by decide +kernel)

private theorem range51From21505 : Win 51 21505 21931 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range51From21505To2239 range51From21505To2341) (join_population range51From21505To2383 range51From21505To2440)) (join_population (join_population range51From21505To2500 range51From21505To2501) (join_population range51From21505To2503 range51From21505To2551)))

private theorem fee51_036_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source036.plan.table+
      4*22428*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*144147773629 := by decide +kernel
private theorem range51From21932To2256 : Segment 51 21932 22428 0 2256 :=
  paid (pc:=78) (v:=144147773629) (by decide) source036_valid tests51_036_0 fee51_036_22428 (by decide +kernel)

private theorem tests51_038_2256 : ∀ z∈source038.plan.table,z.1.Valid 51 2256 := by decide +kernel
private theorem fee51_038_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source038.plan.table+
      4*22428*NaturalPopulation20258.weights source038.extras≤source038.plan.scale*172256382387 := by decide +kernel
private theorem range51From21932To2355 : Segment 51 21932 22428 2256 2355 :=
  paid (pc:=78) (v:=172256382387) (by decide) source038_valid tests51_038_2256 fee51_038_22428 (by decide +kernel)

private theorem tests51_042_2355 : ∀ z∈source042.plan.table,z.1.Valid 51 2355 := by decide +kernel
private theorem fee51_042_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source042.plan.table+
      4*22428*NaturalPopulation20258.weights source042.extras≤source042.plan.scale*210159678354 := by decide +kernel
private theorem range51From21932To2423 : Segment 51 21932 22428 2355 2423 :=
  paid (pc:=77) (v:=210159678354) (by decide) source042_valid tests51_042_2355 fee51_042_22428 (by decide +kernel)

private theorem tests51_044_2423 : ∀ z∈source044.plan.table,z.1.Valid 51 2423 := by decide +kernel
private theorem fee51_044_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source044.plan.table+
      4*22428*NaturalPopulation20258.weights source044.extras≤source044.plan.scale*258610188430 := by decide +kernel
private theorem range51From21932To2450 : Segment 51 21932 22428 2423 2450 :=
  paid (pc:=77) (v:=258610188430) (by decide) source044_valid tests51_044_2423 fee51_044_22428 (by decide +kernel)

private theorem tests51_045_2450 : ∀ z∈source045.plan.table,z.1.Valid 51 2450 := by decide +kernel
private theorem fee51_045_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source045.plan.table+
      4*22428*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*249232141109 := by decide +kernel
private theorem range51From21932To2501 : Segment 51 21932 22428 2450 2501 :=
  paid (pc:=77) (v:=249232141109) (by decide) source045_valid tests51_045_2450 fee51_045_22428 (by decide +kernel)

private theorem range51From21932To2503 : Segment 51 21932 22428 2501 2503 :=
  paid (pc:=77) (v:=249232141109) (by decide) source045_valid tests51_045_2501 fee51_045_22428 (by decide +kernel)

private theorem fee51_046_22428 :
    PopulationFees20258.bill (n:=22428) (PopulationFees20258.tabulate (22428-1) 256) source046.plan.table+
      4*22428*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*235171684009 := by decide +kernel
private theorem range51From21932To2551 : Segment 51 21932 22428 2503 2551 :=
  paid (pc:=76) (v:=235171684009) (by decide) source046_valid tests51_046_2503 fee51_046_22428 (by decide +kernel)

private theorem range51From21932 : Win 51 21932 22428 :=
  complete (by decide) (by decide) (join_population (join_population range51From21932To2256 (join_population range51From21932To2355 range51From21932To2423)) (join_population (join_population range51From21932To2450 range51From21932To2501) (join_population range51From21932To2503 range51From21932To2551)))

private theorem fee51_036_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source036.plan.table+
      4*23015*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*151185703655 := by decide +kernel
private theorem range51From22429To2274 : Segment 51 22429 23015 0 2274 :=
  paid (pc:=78) (v:=151185703655) (by decide) source036_valid tests51_036_0 fee51_036_23015 (by decide +kernel)

private theorem tests51_038_2274 : ∀ z∈source038.plan.table,z.1.Valid 51 2274 := by decide +kernel
private theorem fee51_038_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source038.plan.table+
      4*23015*NaturalPopulation20258.weights source038.extras≤source038.plan.scale*180643202494 := by decide +kernel
private theorem range51From22429To2367 : Segment 51 22429 23015 2274 2367 :=
  paid (pc:=78) (v:=180643202494) (by decide) source038_valid tests51_038_2274 fee51_038_23015 (by decide +kernel)

private theorem tests51_042_2367 : ∀ z∈source042.plan.table,z.1.Valid 51 2367 := by decide +kernel
private theorem fee51_042_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source042.plan.table+
      4*23015*NaturalPopulation20258.weights source042.extras≤source042.plan.scale*220359360647 := by decide +kernel
private theorem range51From22429To2430 : Segment 51 22429 23015 2367 2430 :=
  paid (pc:=77) (v:=220359360647) (by decide) source042_valid tests51_042_2367 fee51_042_23015 (by decide +kernel)

private theorem tests51_043_2430 : ∀ z∈source043.plan.table,z.1.Valid 51 2430 := by decide +kernel
private theorem fee51_043_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source043.plan.table+
      4*23015*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*215138542529 := by decide +kernel
private theorem range51From22429To2454 : Segment 51 22429 23015 2430 2454 :=
  paid (pc:=77) (v:=215138542529) (by decide) source043_valid tests51_043_2430 fee51_043_23015 (by decide +kernel)

private theorem tests51_045_2454 : ∀ z∈source045.plan.table,z.1.Valid 51 2454 := by decide +kernel
private theorem fee51_045_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source045.plan.table+
      4*23015*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*261280892324 := by decide +kernel
private theorem range51From22429To2501 : Segment 51 22429 23015 2454 2501 :=
  paid (pc:=77) (v:=261280892324) (by decide) source045_valid tests51_045_2454 fee51_045_23015 (by decide +kernel)

private theorem range51From22429To2503 : Segment 51 22429 23015 2501 2503 :=
  paid (pc:=77) (v:=261280892324) (by decide) source045_valid tests51_045_2501 fee51_045_23015 (by decide +kernel)

private theorem fee51_046_23015 :
    PopulationFees20258.bill (n:=23015) (PopulationFees20258.tabulate (23015-1) 256) source046.plan.table+
      4*23015*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*246575552212 := by decide +kernel
private theorem range51From22429To2551 : Segment 51 22429 23015 2503 2551 :=
  paid (pc:=76) (v:=246575552212) (by decide) source046_valid tests51_046_2503 fee51_046_23015 (by decide +kernel)

private theorem range51From22429 : Win 51 22429 23015 :=
  complete (by decide) (by decide) (join_population (join_population range51From22429To2274 (join_population range51From22429To2367 range51From22429To2430)) (join_population (join_population range51From22429To2454 range51From22429To2501) (join_population range51From22429To2503 range51From22429To2551)))

theorem cut51From21505 : Win 51 21505 23015 :=
  (join_ground range51From21505 (join_ground range51From21932 range51From22429))

end JSP233.FiniteCutRanges20258
