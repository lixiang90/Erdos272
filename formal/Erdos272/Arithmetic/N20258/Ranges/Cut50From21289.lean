module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source026
public import Erdos272.Arithmetic.N20258.Sources.Source028
public import Erdos272.Arithmetic.N20258.Sources.Source029
public import Erdos272.Arithmetic.N20258.Sources.Source030
public import Erdos272.Arithmetic.N20258.Sources.Source031
public import Erdos272.Arithmetic.N20258.Sources.Source033
public import Erdos272.Arithmetic.N20258.Sources.Source034
public import Erdos272.Arithmetic.N20258.Sources.Source035

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests50_028_0 : ∀ z∈source028.plan.table,z.1.Valid 50 0 := by decide +kernel
private theorem fee50_028_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source028.plan.table+
      4*21672*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*99433098412 := by decide +kernel
private theorem range50From21289To2192 : Segment 50 21289 21672 0 2192 :=
  paid (pc:=79) (v:=99433098412) (by decide) source028_valid tests50_028_0 fee50_028_21672 (by decide +kernel)

private theorem tests50_030_2192 : ∀ z∈source030.plan.table,z.1.Valid 50 2192 := by decide +kernel
private theorem fee50_030_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source030.plan.table+
      4*21672*NaturalPopulation20258.weights source030.extras≤source030.plan.scale*178012690400 := by decide +kernel
private theorem range50From21289To2264 : Segment 50 21289 21672 2192 2264 :=
  paid (pc:=78) (v:=178012690400) (by decide) source030_valid tests50_030_2192 fee50_030_21672 (by decide +kernel)

private theorem tests50_031_2264 : ∀ z∈source031.plan.table,z.1.Valid 50 2264 := by decide +kernel
private theorem fee50_031_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source031.plan.table+
      4*21672*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*164821070446 := by decide +kernel
private theorem range50From21289To2327 : Segment 50 21289 21672 2264 2327 :=
  paid (pc:=78) (v:=164821070446) (by decide) source031_valid tests50_031_2264 fee50_031_21672 (by decide +kernel)

private theorem tests50_034_2327 : ∀ z∈source034.plan.table,z.1.Valid 50 2327 := by decide +kernel
private theorem fee50_034_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source034.plan.table+
      4*21672*NaturalPopulation20258.weights source034.extras≤source034.plan.scale*204055948993 := by decide +kernel
private theorem range50From21289To2381 : Segment 50 21289 21672 2327 2381 :=
  paid (pc:=77) (v:=204055948993) (by decide) source034_valid tests50_034_2327 fee50_034_21672 (by decide +kernel)

private theorem tests50_033_2381 : ∀ z∈source033.plan.table,z.1.Valid 50 2381 := by decide +kernel
private theorem fee50_033_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source033.plan.table+
      4*21672*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*203161275799 := by decide +kernel
private theorem range50From21289To2387 : Segment 50 21289 21672 2381 2387 :=
  paid (pc:=77) (v:=203161275799) (by decide) source033_valid tests50_033_2381 fee50_033_21672 (by decide +kernel)

private theorem tests50_026_2387 : ∀ z∈source026.plan.table,z.1.Valid 50 2387 := by decide +kernel
private theorem fee50_026_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source026.plan.table+
      4*21672*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*200165270760 := by decide +kernel
private theorem range50From21289To2403 : Segment 50 21289 21672 2387 2403 :=
  paid (pc:=77) (v:=200165270760) (by decide) source026_valid tests50_026_2387 fee50_026_21672 (by decide +kernel)

private theorem tests50_026_2403 : ∀ z∈source026.plan.table,z.1.Valid 50 2403 := by decide +kernel
private theorem range50From21289To2405 : Segment 50 21289 21672 2403 2405 :=
  paid (pc:=77) (v:=200165270760) (by decide) source026_valid tests50_026_2403 fee50_026_21672 (by decide +kernel)

private theorem tests50_035_2405 : ∀ z∈source035.plan.table,z.1.Valid 50 2405 := by decide +kernel
private theorem fee50_035_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source035.plan.table+
      4*21672*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*191380427137 := by decide +kernel
private theorem range50From21289To2451 : Segment 50 21289 21672 2405 2451 :=
  paid (pc:=77) (v:=191380427137) (by decide) source035_valid tests50_035_2405 fee50_035_21672 (by decide +kernel)

private theorem range50From21289 : Win 50 21289 21672 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range50From21289To2192 range50From21289To2264) (join_population range50From21289To2327 range50From21289To2381)) (join_population (join_population range50From21289To2387 range50From21289To2403) (join_population range50From21289To2405 range50From21289To2451)))

private theorem fee50_028_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source028.plan.table+
      4*22132*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*103400293556 := by decide +kernel
private theorem range50From21673To2204 : Segment 50 21673 22132 0 2204 :=
  paid (pc:=79) (v:=103400293556) (by decide) source028_valid tests50_028_0 fee50_028_22132 (by decide +kernel)

private theorem tests50_029_2204 : ∀ z∈source029.plan.table,z.1.Valid 50 2204 := by decide +kernel
private theorem fee50_029_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source029.plan.table+
      4*22132*NaturalPopulation20258.weights source029.extras≤source029.plan.scale*183741711725 := by decide +kernel
private theorem range50From21673To2276 : Segment 50 21673 22132 2204 2276 :=
  paid (pc:=78) (v:=183741711725) (by decide) source029_valid tests50_029_2204 fee50_029_22132 (by decide +kernel)

private theorem tests50_031_2276 : ∀ z∈source031.plan.table,z.1.Valid 50 2276 := by decide +kernel
private theorem fee50_031_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source031.plan.table+
      4*22132*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*171317601838 := by decide +kernel
private theorem range50From21673To2333 : Segment 50 21673 22132 2276 2333 :=
  paid (pc:=78) (v:=171317601838) (by decide) source031_valid tests50_031_2276 fee50_031_22132 (by decide +kernel)

private theorem tests50_033_2333 : ∀ z∈source033.plan.table,z.1.Valid 50 2333 := by decide +kernel
private theorem fee50_033_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source033.plan.table+
      4*22132*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*211131747150 := by decide +kernel
private theorem range50From21673To2387 : Segment 50 21673 22132 2333 2387 :=
  paid (pc:=77) (v:=211131747150) (by decide) source033_valid tests50_033_2333 fee50_033_22132 (by decide +kernel)

private theorem fee50_026_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source026.plan.table+
      4*22132*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*207968170744 := by decide +kernel
private theorem range50From21673To2404 : Segment 50 21673 22132 2387 2404 :=
  paid (pc:=77) (v:=207968170744) (by decide) source026_valid tests50_026_2387 fee50_026_22132 (by decide +kernel)

private theorem tests50_035_2404 : ∀ z∈source035.plan.table,z.1.Valid 50 2404 := by decide +kernel
private theorem fee50_035_22132 :
    PopulationFees20258.bill (n:=22132) (PopulationFees20258.tabulate (22132-1) 256) source035.plan.table+
      4*22132*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*198909881061 := by decide +kernel
private theorem range50From21673To2451 : Segment 50 21673 22132 2404 2451 :=
  paid (pc:=77) (v:=198909881061) (by decide) source035_valid tests50_035_2404 fee50_035_22132 (by decide +kernel)

private theorem range50From21673 : Win 50 21673 22132 :=
  complete (by decide) (by decide) (join_population (join_population range50From21673To2204 (join_population range50From21673To2276 range50From21673To2333)) (join_population range50From21673To2387 (join_population range50From21673To2404 range50From21673To2451)))

private theorem fee50_028_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source028.plan.table+
      4*22685*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*108321407052 := by decide +kernel
private theorem range50From22133To2220 : Segment 50 22133 22685 0 2220 :=
  paid (pc:=79) (v:=108321407052) (by decide) source028_valid tests50_028_0 fee50_028_22685 (by decide +kernel)

private theorem tests50_029_2220 : ∀ z∈source029.plan.table,z.1.Valid 50 2220 := by decide +kernel
private theorem fee50_029_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source029.plan.table+
      4*22685*NaturalPopulation20258.weights source029.extras≤source029.plan.scale*192345990160 := by decide +kernel
private theorem range50From22133To2285 : Segment 50 22133 22685 2220 2285 :=
  paid (pc:=78) (v:=192345990160) (by decide) source029_valid tests50_029_2220 fee50_029_22685 (by decide +kernel)

private theorem tests50_031_2285 : ∀ z∈source031.plan.table,z.1.Valid 50 2285 := by decide +kernel
private theorem fee50_031_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source031.plan.table+
      4*22685*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*179375813600 := by decide +kernel
private theorem range50From22133To2340 : Segment 50 22133 22685 2285 2340 :=
  paid (pc:=78) (v:=179375813600) (by decide) source031_valid tests50_031_2285 fee50_031_22685 (by decide +kernel)

private theorem tests50_033_2340 : ∀ z∈source033.plan.table,z.1.Valid 50 2340 := by decide +kernel
private theorem fee50_033_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source033.plan.table+
      4*22685*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*221010538152 := by decide +kernel
private theorem range50From22133To2389 : Segment 50 22133 22685 2340 2389 :=
  paid (pc:=77) (v:=221010538152) (by decide) source033_valid tests50_033_2340 fee50_033_22685 (by decide +kernel)

private theorem tests50_026_2389 : ∀ z∈source026.plan.table,z.1.Valid 50 2389 := by decide +kernel
private theorem fee50_026_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source026.plan.table+
      4*22685*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*217842539449 := by decide +kernel
private theorem range50From22133To2405 : Segment 50 22133 22685 2389 2405 :=
  paid (pc:=77) (v:=217842539449) (by decide) source026_valid tests50_026_2389 fee50_026_22685 (by decide +kernel)

private theorem fee50_035_22685 :
    PopulationFees20258.bill (n:=22685) (PopulationFees20258.tabulate (22685-1) 256) source035.plan.table+
      4*22685*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*208235932232 := by decide +kernel
private theorem range50From22133To2451 : Segment 50 22133 22685 2405 2451 :=
  paid (pc:=77) (v:=208235932232) (by decide) source035_valid tests50_035_2405 fee50_035_22685 (by decide +kernel)

private theorem range50From22133 : Win 50 22133 22685 :=
  complete (by decide) (by decide) (join_population (join_population range50From22133To2220 (join_population range50From22133To2285 range50From22133To2340)) (join_population range50From22133To2389 (join_population range50From22133To2405 range50From22133To2451)))

theorem cut50From21289 : Win 50 21289 22685 :=
  (join_ground range50From21289 (join_ground range50From21673 range50From22133))

end JSP233.FiniteCutRanges20258
