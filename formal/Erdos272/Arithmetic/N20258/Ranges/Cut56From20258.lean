module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source088
public import Erdos272.Arithmetic.N20258.Sources.Source089
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source091
public import Erdos272.Arithmetic.N20258.Sources.Source092

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests56_088_0 : ∀ z∈source088.plan.table,z.1.Valid 56 0 := by decide +kernel
private theorem fee56_088_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source088.plan.table+
      4*20508*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*157227280270 := by decide +kernel
private theorem range56From20258To2503 : Segment 56 20258 20508 0 2503 :=
  paid (pc:=76) (v:=157227280270) (by decide) source088_valid tests56_088_0 fee56_088_20508 (by decide +kernel)

private theorem tests56_088_2503 : ∀ z∈source088.plan.table,z.1.Valid 56 2503 := by decide +kernel
private theorem range56From20258To2521 : Segment 56 20258 20508 2503 2521 :=
  paid (pc:=76) (v:=157227280270) (by decide) source088_valid tests56_088_2503 fee56_088_20508 (by decide +kernel)

private theorem tests56_083_2521 : ∀ z∈source083.plan.table,z.1.Valid 56 2521 := by decide +kernel
private theorem fee56_083_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source083.plan.table+
      4*20508*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*203157986959 := by decide +kernel
private theorem range56From20258To2555 : Segment 56 20258 20508 2521 2555 :=
  paid (pc:=76) (v:=203157986959) (by decide) source083_valid tests56_083_2521 fee56_083_20508 (by decide +kernel)

private theorem tests56_091_2555 : ∀ z∈source091.plan.table,z.1.Valid 56 2555 := by decide +kernel
private theorem fee56_091_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source091.plan.table+
      4*20508*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*241485869062 := by decide +kernel
private theorem range56From20258To2675 : Segment 56 20258 20508 2555 2675 :=
  paid (pc:=74) (v:=241485869062) (by decide) source091_valid tests56_091_2555 fee56_091_20508 (by decide +kernel)

private theorem tests56_089_2675 : ∀ z∈source089.plan.table,z.1.Valid 56 2675 := by decide +kernel
private theorem fee56_089_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source089.plan.table+
      4*20508*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*232768127503 := by decide +kernel
private theorem range56From20258To2761 : Segment 56 20258 20508 2675 2761 :=
  paid (pc:=74) (v:=232768127503) (by decide) source089_valid tests56_089_2675 fee56_089_20508 (by decide +kernel)

private theorem tests56_085_2761 : ∀ z∈source085.plan.table,z.1.Valid 56 2761 := by decide +kernel
private theorem fee56_085_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source085.plan.table+
      4*20508*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*223521563702 := by decide +kernel
private theorem range56From20258To2855 : Segment 56 20258 20508 2761 2855 :=
  paid (pc:=73) (v:=223521563702) (by decide) source085_valid tests56_085_2761 fee56_085_20508 (by decide +kernel)

private theorem tests56_087_2855 : ∀ z∈source087.plan.table,z.1.Valid 56 2855 := by decide +kernel
private theorem fee56_087_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source087.plan.table+
      4*20508*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*207350218278 := by decide +kernel
private theorem range56From20258To3022 : Segment 56 20258 20508 2855 3022 :=
  paid (pc:=71) (v:=207350218278) (by decide) source087_valid tests56_087_2855 fee56_087_20508 (by decide +kernel)

private theorem tests56_090_3022 : ∀ z∈source090.plan.table,z.1.Valid 56 3022 := by decide +kernel
private theorem fee56_090_20508 :
    PopulationFees20258.bill (n:=20508) (PopulationFees20258.tabulate (20508-1) 256) source090.plan.table+
      4*20508*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*191176160081 := by decide +kernel
private theorem range56From20258To3081 : Segment 56 20258 20508 3022 3081 :=
  paid (pc:=70) (v:=191176160081) (by decide) source090_valid tests56_090_3022 fee56_090_20508 (by decide +kernel)

private theorem range56From20258 : Win 56 20258 20508 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range56From20258To2503 range56From20258To2521) (join_population range56From20258To2555 range56From20258To2675)) (join_population (join_population range56From20258To2761 range56From20258To2855) (join_population range56From20258To3022 range56From20258To3081)))

private theorem fee56_088_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source088.plan.table+
      4*20796*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*161332324563 := by decide +kernel
private theorem range56From20509To2503 : Segment 56 20509 20796 0 2503 :=
  paid (pc:=76) (v:=161332324563) (by decide) source088_valid tests56_088_0 fee56_088_20796 (by decide +kernel)

private theorem range56From20509To2521 : Segment 56 20509 20796 2503 2521 :=
  paid (pc:=76) (v:=161332324563) (by decide) source088_valid tests56_088_2503 fee56_088_20796 (by decide +kernel)

private theorem fee56_083_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source083.plan.table+
      4*20796*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*208403960186 := by decide +kernel
private theorem range56From20509To2551 : Segment 56 20509 20796 2521 2551 :=
  paid (pc:=76) (v:=208403960186) (by decide) source083_valid tests56_083_2521 fee56_083_20796 (by decide +kernel)

private theorem tests56_083_2551 : ∀ z∈source083.plan.table,z.1.Valid 56 2551 := by decide +kernel
private theorem range56From20509To2552 : Segment 56 20509 20796 2551 2552 :=
  paid (pc:=76) (v:=208403960186) (by decide) source083_valid tests56_083_2551 fee56_083_20796 (by decide +kernel)

private theorem tests56_091_2552 : ∀ z∈source091.plan.table,z.1.Valid 56 2552 := by decide +kernel
private theorem fee56_091_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source091.plan.table+
      4*20796*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*247695689441 := by decide +kernel
private theorem range56From20509To2660 : Segment 56 20509 20796 2552 2660 :=
  paid (pc:=75) (v:=247695689441) (by decide) source091_valid tests56_091_2552 fee56_091_20796 (by decide +kernel)

private theorem tests56_089_2660 : ∀ z∈source089.plan.table,z.1.Valid 56 2660 := by decide +kernel
private theorem fee56_089_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source089.plan.table+
      4*20796*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*238767325111 := by decide +kernel
private theorem range56From20509To2743 : Segment 56 20509 20796 2660 2743 :=
  paid (pc:=74) (v:=238767325111) (by decide) source089_valid tests56_089_2660 fee56_089_20796 (by decide +kernel)

private theorem tests56_085_2743 : ∀ z∈source085.plan.table,z.1.Valid 56 2743 := by decide +kernel
private theorem fee56_085_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source085.plan.table+
      4*20796*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*229296136303 := by decide +kernel
private theorem range56From20509To2830 : Segment 56 20509 20796 2743 2830 :=
  paid (pc:=73) (v:=229296136303) (by decide) source085_valid tests56_085_2743 fee56_085_20796 (by decide +kernel)

private theorem tests56_092_2830 : ∀ z∈source092.plan.table,z.1.Valid 56 2830 := by decide +kernel
private theorem fee56_092_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source092.plan.table+
      4*20796*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*213504422270 := by decide +kernel
private theorem range56From20509To2984 : Segment 56 20509 20796 2830 2984 :=
  paid (pc:=72) (v:=213504422270) (by decide) source092_valid tests56_092_2830 fee56_092_20796 (by decide +kernel)

private theorem tests56_090_2984 : ∀ z∈source090.plan.table,z.1.Valid 56 2984 := by decide +kernel
private theorem fee56_090_20796 :
    PopulationFees20258.bill (n:=20796) (PopulationFees20258.tabulate (20796-1) 256) source090.plan.table+
      4*20796*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*196162382119 := by decide +kernel
private theorem range56From20509To3081 : Segment 56 20509 20796 2984 3081 :=
  paid (pc:=71) (v:=196162382119) (by decide) source090_valid tests56_090_2984 fee56_090_20796 (by decide +kernel)

private theorem range56From20509 : Win 56 20509 20796 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range56From20509To2503 range56From20509To2521) (join_population range56From20509To2551 range56From20509To2552)) (join_population (join_population range56From20509To2660 range56From20509To2743) (join_population range56From20509To2830 (join_population range56From20509To2984 range56From20509To3081))))

theorem cut56From20258 : Win 56 20258 20796 :=
  (join_ground range56From20258 range56From20509)

end JSP233.FiniteCutRanges20258
