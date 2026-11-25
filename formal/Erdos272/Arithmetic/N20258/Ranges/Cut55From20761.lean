module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source075
public import Erdos272.Arithmetic.N20258.Sources.Source078
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source084
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086
public import Erdos272.Arithmetic.N20258.Sources.Source087

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source082.plan.table+
      4*21042*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*133122887326 := by decide +kernel
private theorem range55From20761To2418 : Segment 55 20761 21042 0 2418 :=
  paid (pc:=77) (v:=133122887326) (by decide) source082_valid tests55_082_0 fee55_082_21042 (by decide +kernel)

private theorem tests55_075_2418 : ∀ z∈source075.plan.table,z.1.Valid 55 2418 := by decide +kernel
private theorem fee55_075_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source075.plan.table+
      4*21042*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*179035496977 := by decide +kernel
private theorem range55From20761To2455 : Segment 55 20761 21042 2418 2455 :=
  paid (pc:=77) (v:=179035496977) (by decide) source075_valid tests55_075_2418 fee55_075_21042 (by decide +kernel)

private theorem tests55_084_2455 : ∀ z∈source084.plan.table,z.1.Valid 55 2455 := by decide +kernel
private theorem fee55_084_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source084.plan.table+
      4*21042*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*220405207104 := by decide +kernel
private theorem range55From20761To2518 : Segment 55 20761 21042 2455 2518 :=
  paid (pc:=76) (v:=220405207104) (by decide) source084_valid tests55_084_2455 fee55_084_21042 (by decide +kernel)

private theorem tests55_083_2518 : ∀ z∈source083.plan.table,z.1.Valid 55 2518 := by decide +kernel
private theorem fee55_083_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source083.plan.table+
      4*21042*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*212904234025 := by decide +kernel
private theorem range55From20761To2570 : Segment 55 20761 21042 2518 2570 :=
  paid (pc:=76) (v:=212904234025) (by decide) source083_valid tests55_083_2518 fee55_083_21042 (by decide +kernel)

private theorem tests55_086_2570 : ∀ z∈source086.plan.table,z.1.Valid 55 2570 := by decide +kernel
private theorem fee55_086_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source086.plan.table+
      4*21042*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*253581536186 := by decide +kernel
private theorem range55From20761To2672 : Segment 55 20761 21042 2570 2672 :=
  paid (pc:=75) (v:=253581536186) (by decide) source086_valid tests55_086_2570 fee55_086_21042 (by decide +kernel)

private theorem tests55_078_2672 : ∀ z∈source078.plan.table,z.1.Valid 55 2672 := by decide +kernel
private theorem fee55_078_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source078.plan.table+
      4*21042*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*198413573865 := by decide +kernel
private theorem range55From20761To2676 : Segment 55 20761 21042 2672 2676 :=
  paid (pc:=75) (v:=198413573865) (by decide) source078_valid tests55_078_2672 fee55_078_21042 (by decide +kernel)

private theorem tests55_085_2676 : ∀ z∈source085.plan.table,z.1.Valid 55 2676 := by decide +kernel
private theorem fee55_085_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source085.plan.table+
      4*21042*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*234229441616 := by decide +kernel
private theorem range55From20761To2839 : Segment 55 20761 21042 2676 2839 :=
  paid (pc:=73) (v:=234229441616) (by decide) source085_valid tests55_085_2676 fee55_085_21042 (by decide +kernel)

private theorem tests55_087_2839 : ∀ z∈source087.plan.table,z.1.Valid 55 2839 := by decide +kernel
private theorem fee55_087_21042 :
    PopulationFees20258.bill (n:=21042) (PopulationFees20258.tabulate (21042-1) 256) source087.plan.table+
      4*21042*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*217344679035 := by decide +kernel
private theorem range55From20761To2971 : Segment 55 20761 21042 2839 2971 :=
  paid (pc:=72) (v:=217344679035) (by decide) source087_valid tests55_087_2839 fee55_087_21042 (by decide +kernel)

private theorem range55From20761 : Win 55 20761 21042 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range55From20761To2418 range55From20761To2455) (join_population range55From20761To2518 range55From20761To2570)) (join_population (join_population range55From20761To2672 range55From20761To2676) (join_population range55From20761To2839 range55From20761To2971)))

private theorem fee55_082_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source082.plan.table+
      4*21352*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*136705893094 := by decide +kernel
private theorem range55From21043To2431 : Segment 55 21043 21352 0 2431 :=
  paid (pc:=77) (v:=136705893094) (by decide) source082_valid tests55_082_0 fee55_082_21352 (by decide +kernel)

private theorem tests55_084_2431 : ∀ z∈source084.plan.table,z.1.Valid 55 2431 := by decide +kernel
private theorem fee55_084_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source084.plan.table+
      4*21352*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*226255806347 := by decide +kernel
private theorem range55From21043To2523 : Segment 55 21043 21352 2431 2523 :=
  paid (pc:=76) (v:=226255806347) (by decide) source084_valid tests55_084_2431 fee55_084_21352 (by decide +kernel)

private theorem tests55_083_2523 : ∀ z∈source083.plan.table,z.1.Valid 55 2523 := by decide +kernel
private theorem fee55_083_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source083.plan.table+
      4*21352*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*218568859910 := by decide +kernel
private theorem range55From21043To2574 : Segment 55 21043 21352 2523 2574 :=
  paid (pc:=76) (v:=218568859910) (by decide) source083_valid tests55_083_2523 fee55_083_21352 (by decide +kernel)

private theorem tests55_086_2574 : ∀ z∈source086.plan.table,z.1.Valid 55 2574 := by decide +kernel
private theorem fee55_086_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source086.plan.table+
      4*21352*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*260317474003 := by decide +kernel
private theorem range55From21043To2668 : Segment 55 21043 21352 2574 2668 :=
  paid (pc:=75) (v:=260317474003) (by decide) source086_valid tests55_086_2574 fee55_086_21352 (by decide +kernel)

private theorem tests55_078_2668 : ∀ z∈source078.plan.table,z.1.Valid 55 2668 := by decide +kernel
private theorem fee55_078_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source078.plan.table+
      4*21352*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*203845222292 := by decide +kernel
private theorem range55From21043To2676 : Segment 55 21043 21352 2668 2676 :=
  paid (pc:=75) (v:=203845222292) (by decide) source078_valid tests55_078_2668 fee55_078_21352 (by decide +kernel)

private theorem fee55_085_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source085.plan.table+
      4*21352*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*240475927060 := by decide +kernel
private theorem range55From21043To2829 : Segment 55 21043 21352 2676 2829 :=
  paid (pc:=74) (v:=240475927060) (by decide) source085_valid tests55_085_2676 fee55_085_21352 (by decide +kernel)

private theorem tests55_087_2829 : ∀ z∈source087.plan.table,z.1.Valid 55 2829 := by decide +kernel
private theorem fee55_087_21352 :
    PopulationFees20258.bill (n:=21352) (PopulationFees20258.tabulate (21352-1) 256) source087.plan.table+
      4*21352*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*223140194641 := by decide +kernel
private theorem range55From21043To2971 : Segment 55 21043 21352 2829 2971 :=
  paid (pc:=72) (v:=223140194641) (by decide) source087_valid tests55_087_2829 fee55_087_21352 (by decide +kernel)

private theorem range55From21043 : Win 55 21043 21352 :=
  complete (by decide) (by decide) (join_population (join_population range55From21043To2431 (join_population range55From21043To2523 range55From21043To2574)) (join_population (join_population range55From21043To2668 range55From21043To2676) (join_population range55From21043To2829 range55From21043To2971)))

private theorem fee55_082_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source082.plan.table+
      4*21698*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*140850957716 := by decide +kernel
private theorem range55From21353To2442 : Segment 55 21353 21698 0 2442 :=
  paid (pc:=77) (v:=140850957716) (by decide) source082_valid tests55_082_0 fee55_082_21698 (by decide +kernel)

private theorem tests55_084_2442 : ∀ z∈source084.plan.table,z.1.Valid 55 2442 := by decide +kernel
private theorem fee55_084_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source084.plan.table+
      4*21698*NaturalPopulation20258.weights source084.extras≤source084.plan.scale*233008286327 := by decide +kernel
private theorem range55From21353To2526 : Segment 55 21353 21698 2442 2526 :=
  paid (pc:=76) (v:=233008286327) (by decide) source084_valid tests55_084_2442 fee55_084_21698 (by decide +kernel)

private theorem tests55_083_2526 : ∀ z∈source083.plan.table,z.1.Valid 55 2526 := by decide +kernel
private theorem fee55_083_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source083.plan.table+
      4*21698*NaturalPopulation20258.weights source083.extras≤source083.plan.scale*225097569676 := by decide +kernel
private theorem range55From21353To2577 : Segment 55 21353 21698 2526 2577 :=
  paid (pc:=76) (v:=225097569676) (by decide) source083_valid tests55_083_2526 fee55_083_21698 (by decide +kernel)

private theorem tests55_086_2577 : ∀ z∈source086.plan.table,z.1.Valid 55 2577 := by decide +kernel
private theorem fee55_086_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source086.plan.table+
      4*21698*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*268045955836 := by decide +kernel
private theorem range55From21353To2662 : Segment 55 21353 21698 2577 2662 :=
  paid (pc:=75) (v:=268045955836) (by decide) source086_valid tests55_086_2577 fee55_086_21698 (by decide +kernel)

private theorem tests55_078_2662 : ∀ z∈source078.plan.table,z.1.Valid 55 2662 := by decide +kernel
private theorem fee55_078_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source078.plan.table+
      4*21698*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*209863177834 := by decide +kernel
private theorem range55From21353To2676 : Segment 55 21353 21698 2662 2676 :=
  paid (pc:=75) (v:=209863177834) (by decide) source078_valid tests55_078_2662 fee55_078_21698 (by decide +kernel)

private theorem fee55_085_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source085.plan.table+
      4*21698*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*247628128195 := by decide +kernel
private theorem range55From21353To2818 : Segment 55 21353 21698 2676 2818 :=
  paid (pc:=74) (v:=247628128195) (by decide) source085_valid tests55_085_2676 fee55_085_21698 (by decide +kernel)

private theorem tests55_087_2818 : ∀ z∈source087.plan.table,z.1.Valid 55 2818 := by decide +kernel
private theorem fee55_087_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source087.plan.table+
      4*21698*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*229814526691 := by decide +kernel
private theorem range55From21353To2962 : Segment 55 21353 21698 2818 2962 :=
  paid (pc:=73) (v:=229814526691) (by decide) source087_valid tests55_087_2818 fee55_087_21698 (by decide +kernel)

private theorem tests55_080_2962 : ∀ z∈source080.plan.table,z.1.Valid 55 2962 := by decide +kernel
private theorem fee55_080_21698 :
    PopulationFees20258.bill (n:=21698) (PopulationFees20258.tabulate (21698-1) 256) source080.plan.table+
      4*21698*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*227325940506 := by decide +kernel
private theorem range55From21353To2971 : Segment 55 21353 21698 2962 2971 :=
  paid (pc:=73) (v:=227325940506) (by decide) source080_valid tests55_080_2962 fee55_080_21698 (by decide +kernel)

private theorem range55From21353 : Win 55 21353 21698 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range55From21353To2442 range55From21353To2526) (join_population range55From21353To2577 range55From21353To2662)) (join_population (join_population range55From21353To2676 range55From21353To2818) (join_population range55From21353To2962 range55From21353To2971)))

theorem cut55From20761 : Win 55 20761 21698 :=
  (join_ground range55From20761 (join_ground range55From21043 range55From21353))

end JSP233.FiniteCutRanges20258
