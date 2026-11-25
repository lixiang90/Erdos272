module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source101
public import Erdos272.Arithmetic.N20258.Sources.Source102

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests59_101_0 : ∀ z∈source101.plan.table,z.1.Valid 59 0 := by decide +kernel
private theorem fee59_101_22015 :
    PopulationFees20258.bill (n:=22015) (PopulationFees20258.tabulate (22015-1) 256) source101.plan.table+
      4*22015*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*187995847753 := by decide +kernel
private theorem range59From21673To2832 : Segment 59 21673 22015 0 2832 :=
  paid (pc:=74) (v:=187995847753) (by decide) source101_valid tests59_101_0 fee59_101_22015 (by decide +kernel)

private theorem tests59_101_2832 : ∀ z∈source101.plan.table,z.1.Valid 59 2832 := by decide +kernel
private theorem range59From21673To2856 : Segment 59 21673 22015 2832 2856 :=
  paid (pc:=74) (v:=187995847753) (by decide) source101_valid tests59_101_2832 fee59_101_22015 (by decide +kernel)

private theorem tests59_101_2856 : ∀ z∈source101.plan.table,z.1.Valid 59 2856 := by decide +kernel
private theorem range59From21673To2858 : Segment 59 21673 22015 2856 2858 :=
  paid (pc:=74) (v:=187995847753) (by decide) source101_valid tests59_101_2856 fee59_101_22015 (by decide +kernel)

private theorem tests59_100_2858 : ∀ z∈source100.plan.table,z.1.Valid 59 2858 := by decide +kernel
private theorem fee59_100_22015 :
    PopulationFees20258.bill (n:=22015) (PopulationFees20258.tabulate (22015-1) 256) source100.plan.table+
      4*22015*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*279619653964 := by decide +kernel
private theorem range59From21673To3142 : Segment 59 21673 22015 2858 3142 :=
  paid (pc:=72) (v:=279619653964) (by decide) source100_valid tests59_100_2858 fee59_100_22015 (by decide +kernel)

private theorem tests59_096_3142 : ∀ z∈source096.plan.table,z.1.Valid 59 3142 := by decide +kernel
private theorem fee59_096_22015 :
    PopulationFees20258.bill (n:=22015) (PopulationFees20258.tabulate (22015-1) 256) source096.plan.table+
      4*22015*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*244701593696 := by decide +kernel
private theorem range59From21673To3423 : Segment 59 21673 22015 3142 3423 :=
  paid (pc:=69) (v:=244701593696) (by decide) source096_valid tests59_096_3142 fee59_096_22015 (by decide +kernel)

private theorem range59From21673 : Win 59 21673 22015 :=
  complete (by decide) (by decide) (join_population (join_population range59From21673To2832 range59From21673To2856) (join_population range59From21673To2858 (join_population range59From21673To3142 range59From21673To3423)))

private theorem fee59_101_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source101.plan.table+
      4*22393*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*193906999257 := by decide +kernel
private theorem range59From22016To2834 : Segment 59 22016 22393 0 2834 :=
  paid (pc:=74) (v:=193906999257) (by decide) source101_valid tests59_101_0 fee59_101_22393 (by decide +kernel)

private theorem tests59_101_2834 : ∀ z∈source101.plan.table,z.1.Valid 59 2834 := by decide +kernel
private theorem range59From22016To2856 : Segment 59 22016 22393 2834 2856 :=
  paid (pc:=74) (v:=193906999257) (by decide) source101_valid tests59_101_2834 fee59_101_22393 (by decide +kernel)

private theorem range59From22016To2858 : Segment 59 22016 22393 2856 2858 :=
  paid (pc:=74) (v:=193906999257) (by decide) source101_valid tests59_101_2856 fee59_101_22393 (by decide +kernel)

private theorem fee59_100_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source100.plan.table+
      4*22393*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*288245534006 := by decide +kernel
private theorem range59From22016To3114 : Segment 59 22016 22393 2858 3114 :=
  paid (pc:=72) (v:=288245534006) (by decide) source100_valid tests59_100_2858 fee59_100_22393 (by decide +kernel)

private theorem tests59_102_3114 : ∀ z∈source102.plan.table,z.1.Valid 59 3114 := by decide +kernel
private theorem fee59_102_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source102.plan.table+
      4*22393*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*262398986610 := by decide +kernel
private theorem range59From22016To3358 : Segment 59 22016 22393 3114 3358 :=
  paid (pc:=70) (v:=262398986610) (by decide) source102_valid tests59_102_3114 fee59_102_22393 (by decide +kernel)

private theorem tests59_096_3358 : ∀ z∈source096.plan.table,z.1.Valid 59 3358 := by decide +kernel
private theorem fee59_096_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source096.plan.table+
      4*22393*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*252532852920 := by decide +kernel
private theorem range59From22016To3423 : Segment 59 22016 22393 3358 3423 :=
  paid (pc:=69) (v:=252532852920) (by decide) source096_valid tests59_096_3358 fee59_096_22393 (by decide +kernel)

private theorem range59From22016 : Win 59 22016 22393 :=
  complete (by decide) (by decide) (join_population (join_population range59From22016To2834 (join_population range59From22016To2856 range59From22016To2858)) (join_population range59From22016To3114 (join_population range59From22016To3358 range59From22016To3423)))

private theorem fee59_101_22800 :
    PopulationFees20258.bill (n:=22800) (PopulationFees20258.tabulate (22800-1) 256) source101.plan.table+
      4*22800*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*200378465310 := by decide +kernel
private theorem range59From22394To2842 : Segment 59 22394 22800 0 2842 :=
  paid (pc:=75) (v:=200378465310) (by decide) source101_valid tests59_101_0 fee59_101_22800 (by decide +kernel)

private theorem tests59_101_2842 : ∀ z∈source101.plan.table,z.1.Valid 59 2842 := by decide +kernel
private theorem range59From22394To2864 : Segment 59 22394 22800 2842 2864 :=
  paid (pc:=75) (v:=200378465310) (by decide) source101_valid tests59_101_2842 fee59_101_22800 (by decide +kernel)

private theorem tests59_100_2864 : ∀ z∈source100.plan.table,z.1.Valid 59 2864 := by decide +kernel
private theorem fee59_100_22800 :
    PopulationFees20258.bill (n:=22800) (PopulationFees20258.tabulate (22800-1) 256) source100.plan.table+
      4*22800*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*297945960280 := by decide +kernel
private theorem range59From22394To3096 : Segment 59 22394 22800 2864 3096 :=
  paid (pc:=73) (v:=297945960280) (by decide) source100_valid tests59_100_2864 fee59_100_22800 (by decide +kernel)

private theorem tests59_102_3096 : ∀ z∈source102.plan.table,z.1.Valid 59 3096 := by decide +kernel
private theorem fee59_102_22800 :
    PopulationFees20258.bill (n:=22800) (PopulationFees20258.tabulate (22800-1) 256) source102.plan.table+
      4*22800*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*271092975972 := by decide +kernel
private theorem range59From22394To3325 : Segment 59 22394 22800 3096 3325 :=
  paid (pc:=71) (v:=271092975972) (by decide) source102_valid tests59_102_3096 fee59_102_22800 (by decide +kernel)

private theorem tests59_096_3325 : ∀ z∈source096.plan.table,z.1.Valid 59 3325 := by decide +kernel
private theorem fee59_096_22800 :
    PopulationFees20258.bill (n:=22800) (PopulationFees20258.tabulate (22800-1) 256) source096.plan.table+
      4*22800*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*261024938085 := by decide +kernel
private theorem range59From22394To3421 : Segment 59 22394 22800 3325 3421 :=
  paid (pc:=70) (v:=261024938085) (by decide) source096_valid tests59_096_3325 fee59_096_22800 (by decide +kernel)

private theorem tests59_096_3421 : ∀ z∈source096.plan.table,z.1.Valid 59 3421 := by decide +kernel
private theorem range59From22394To3423 : Segment 59 22394 22800 3421 3423 :=
  paid (pc:=70) (v:=261024938085) (by decide) source096_valid tests59_096_3421 fee59_096_22800 (by decide +kernel)

private theorem range59From22394 : Win 59 22394 22800 :=
  complete (by decide) (by decide) (join_population (join_population range59From22394To2842 (join_population range59From22394To2864 range59From22394To3096)) (join_population range59From22394To3325 (join_population range59From22394To3421 range59From22394To3423)))

private theorem fee59_101_23184 :
    PopulationFees20258.bill (n:=23184) (PopulationFees20258.tabulate (23184-1) 256) source101.plan.table+
      4*23184*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*206597225582 := by decide +kernel
private theorem range59From22801To2876 : Segment 59 22801 23184 0 2876 :=
  paid (pc:=75) (v:=206597225582) (by decide) source101_valid tests59_101_0 fee59_101_23184 (by decide +kernel)

private theorem tests59_100_2876 : ∀ z∈source100.plan.table,z.1.Valid 59 2876 := by decide +kernel
private theorem fee59_100_23184 :
    PopulationFees20258.bill (n:=23184) (PopulationFees20258.tabulate (23184-1) 256) source100.plan.table+
      4*23184*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*306842300432 := by decide +kernel
private theorem range59From22801To3117 : Segment 59 22801 23184 2876 3117 :=
  paid (pc:=73) (v:=306842300432) (by decide) source100_valid tests59_100_2876 fee59_100_23184 (by decide +kernel)

private theorem tests59_102_3117 : ∀ z∈source102.plan.table,z.1.Valid 59 3117 := by decide +kernel
private theorem fee59_102_23184 :
    PopulationFees20258.bill (n:=23184) (PopulationFees20258.tabulate (23184-1) 256) source102.plan.table+
      4*23184*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*279407433101 := by decide +kernel
private theorem range59From22801To3331 : Segment 59 22801 23184 3117 3331 :=
  paid (pc:=71) (v:=279407433101) (by decide) source102_valid tests59_102_3117 fee59_102_23184 (by decide +kernel)

private theorem tests59_096_3331 : ∀ z∈source096.plan.table,z.1.Valid 59 3331 := by decide +kernel
private theorem fee59_096_23184 :
    PopulationFees20258.bill (n:=23184) (PopulationFees20258.tabulate (23184-1) 256) source096.plan.table+
      4*23184*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*268989506116 := by decide +kernel
private theorem range59From22801To3421 : Segment 59 22801 23184 3331 3421 :=
  paid (pc:=71) (v:=268989506116) (by decide) source096_valid tests59_096_3331 fee59_096_23184 (by decide +kernel)

private theorem range59From22801To3423 : Segment 59 22801 23184 3421 3423 :=
  paid (pc:=71) (v:=268989506116) (by decide) source096_valid tests59_096_3421 fee59_096_23184 (by decide +kernel)

private theorem range59From22801 : Win 59 22801 23184 :=
  complete (by decide) (by decide) (join_population (join_population range59From22801To2876 range59From22801To3117) (join_population range59From22801To3331 (join_population range59From22801To3421 range59From22801To3423)))

theorem cut59From21673 : Win 59 21673 23184 :=
  (join_ground (join_ground range59From21673 range59From22016) (join_ground range59From22394 range59From22801))

end JSP233.FiniteCutRanges20258
