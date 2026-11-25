module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source100

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests58_098_0 : ∀ z∈source098.plan.table,z.1.Valid 58 0 := by decide +kernel
private theorem fee58_098_20601 :
    PopulationFees20258.bill (n:=20601) (PopulationFees20258.tabulate (20601-1) 256) source098.plan.table+
      4*20601*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*178612893584 := by decide +kernel
private theorem range58From20258To2684 : Segment 58 20258 20601 0 2684 :=
  paid (pc:=74) (v:=178612893584) (by decide) source098_valid tests58_098_0 fee58_098_20601 (by decide +kernel)

private theorem tests58_095_2684 : ∀ z∈source095.plan.table,z.1.Valid 58 2684 := by decide +kernel
private theorem fee58_095_20601 :
    PopulationFees20258.bill (n:=20601) (PopulationFees20258.tabulate (20601-1) 256) source095.plan.table+
      4*20601*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*229683509802 := by decide +kernel
private theorem range58From20258To2744 : Segment 58 20258 20601 2684 2744 :=
  paid (pc:=73) (v:=229683509802) (by decide) source095_valid tests58_095_2684 fee58_095_20601 (by decide +kernel)

private theorem tests58_094_2744 : ∀ z∈source094.plan.table,z.1.Valid 58 2744 := by decide +kernel
private theorem fee58_094_20601 :
    PopulationFees20258.bill (n:=20601) (PopulationFees20258.tabulate (20601-1) 256) source094.plan.table+
      4*20601*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*223016070718 := by decide +kernel
private theorem range58From20258To2810 : Segment 58 20258 20601 2744 2810 :=
  paid (pc:=73) (v:=223016070718) (by decide) source094_valid tests58_094_2744 fee58_094_20601 (by decide +kernel)

private theorem tests58_094_2810 : ∀ z∈source094.plan.table,z.1.Valid 58 2810 := by decide +kernel
private theorem range58From20258To2812 : Segment 58 20258 20601 2810 2812 :=
  paid (pc:=73) (v:=223016070718) (by decide) source094_valid tests58_094_2810 fee58_094_20601 (by decide +kernel)

private theorem tests58_100_2812 : ∀ z∈source100.plan.table,z.1.Valid 58 2812 := by decide +kernel
private theorem fee58_100_20601 :
    PopulationFees20258.bill (n:=20601) (PopulationFees20258.tabulate (20601-1) 256) source100.plan.table+
      4*20601*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*248038783537 := by decide +kernel
private theorem range58From20258To3246 : Segment 58 20258 20601 2812 3246 :=
  paid (pc:=69) (v:=248038783537) (by decide) source100_valid tests58_100_2812 fee58_100_20601 (by decide +kernel)

private theorem tests58_096_3246 : ∀ z∈source096.plan.table,z.1.Valid 58 3246 := by decide +kernel
private theorem fee58_096_20601 :
    PopulationFees20258.bill (n:=20601) (PopulationFees20258.tabulate (20601-1) 256) source096.plan.table+
      4*20601*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*216936887443 := by decide +kernel
private theorem range58From20258To3307 : Segment 58 20258 20601 3246 3307 :=
  paid (pc:=67) (v:=216936887443) (by decide) source096_valid tests58_096_3246 fee58_096_20601 (by decide +kernel)

private theorem range58From20258 : Win 58 20258 20601 :=
  complete (by decide) (by decide) (join_population (join_population range58From20258To2684 (join_population range58From20258To2744 range58From20258To2810)) (join_population range58From20258To2812 (join_population range58From20258To3246 range58From20258To3307)))

private theorem fee58_098_20952 :
    PopulationFees20258.bill (n:=20952) (PopulationFees20258.tabulate (20952-1) 256) source098.plan.table+
      4*20952*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*184188427911 := by decide +kernel
private theorem range58From20602To2695 : Segment 58 20602 20952 0 2695 :=
  paid (pc:=74) (v:=184188427911) (by decide) source098_valid tests58_098_0 fee58_098_20952 (by decide +kernel)

private theorem tests58_095_2695 : ∀ z∈source095.plan.table,z.1.Valid 58 2695 := by decide +kernel
private theorem fee58_095_20952 :
    PopulationFees20258.bill (n:=20952) (PopulationFees20258.tabulate (20952-1) 256) source095.plan.table+
      4*20952*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*236738207832 := by decide +kernel
private theorem range58From20602To2748 : Segment 58 20602 20952 2695 2748 :=
  paid (pc:=74) (v:=236738207832) (by decide) source095_valid tests58_095_2695 fee58_095_20952 (by decide +kernel)

private theorem tests58_094_2748 : ∀ z∈source094.plan.table,z.1.Valid 58 2748 := by decide +kernel
private theorem fee58_094_20952 :
    PopulationFees20258.bill (n:=20952) (PopulationFees20258.tabulate (20952-1) 256) source094.plan.table+
      4*20952*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*229878133587 := by decide +kernel
private theorem range58From20602To2811 : Segment 58 20602 20952 2748 2811 :=
  paid (pc:=73) (v:=229878133587) (by decide) source094_valid tests58_094_2748 fee58_094_20952 (by decide +kernel)

private theorem tests58_094_2811 : ∀ z∈source094.plan.table,z.1.Valid 58 2811 := by decide +kernel
private theorem range58From20602To2813 : Segment 58 20602 20952 2811 2813 :=
  paid (pc:=73) (v:=229878133587) (by decide) source094_valid tests58_094_2811 fee58_094_20952 (by decide +kernel)

private theorem tests58_100_2813 : ∀ z∈source100.plan.table,z.1.Valid 58 2813 := by decide +kernel
private theorem fee58_100_20952 :
    PopulationFees20258.bill (n:=20952) (PopulationFees20258.tabulate (20952-1) 256) source100.plan.table+
      4*20952*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*255672524414 := by decide +kernel
private theorem range58From20602To3199 : Segment 58 20602 20952 2813 3199 :=
  paid (pc:=70) (v:=255672524414) (by decide) source100_valid tests58_100_2813 fee58_100_20952 (by decide +kernel)

private theorem tests58_096_3199 : ∀ z∈source096.plan.table,z.1.Valid 58 3199 := by decide +kernel
private theorem fee58_096_20952 :
    PopulationFees20258.bill (n:=20952) (PopulationFees20258.tabulate (20952-1) 256) source096.plan.table+
      4*20952*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*223647234667 := by decide +kernel
private theorem range58From20602To3307 : Segment 58 20602 20952 3199 3307 :=
  paid (pc:=68) (v:=223647234667) (by decide) source096_valid tests58_096_3199 fee58_096_20952 (by decide +kernel)

private theorem range58From20602 : Win 58 20602 20952 :=
  complete (by decide) (by decide) (join_population (join_population range58From20602To2695 (join_population range58From20602To2748 range58From20602To2811)) (join_population range58From20602To2813 (join_population range58From20602To3199 range58From20602To3307)))

private theorem fee58_098_21316 :
    PopulationFees20258.bill (n:=21316) (PopulationFees20258.tabulate (21316-1) 256) source098.plan.table+
      4*21316*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*190109768121 := by decide +kernel
private theorem range58From20953To2704 : Segment 58 20953 21316 0 2704 :=
  paid (pc:=74) (v:=190109768121) (by decide) source098_valid tests58_098_0 fee58_098_21316 (by decide +kernel)

private theorem tests58_094_2704 : ∀ z∈source094.plan.table,z.1.Valid 58 2704 := by decide +kernel
private theorem fee58_094_21316 :
    PopulationFees20258.bill (n:=21316) (PopulationFees20258.tabulate (21316-1) 256) source094.plan.table+
      4*21316*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*237166767250 := by decide +kernel
private theorem range58From20953To2808 : Segment 58 20953 21316 2704 2808 :=
  paid (pc:=74) (v:=237166767250) (by decide) source094_valid tests58_094_2704 fee58_094_21316 (by decide +kernel)

private theorem tests58_094_2808 : ∀ z∈source094.plan.table,z.1.Valid 58 2808 := by decide +kernel
private theorem range58From20953To2812 : Segment 58 20953 21316 2808 2812 :=
  paid (pc:=73) (v:=237166767250) (by decide) source094_valid tests58_094_2808 fee58_094_21316 (by decide +kernel)

private theorem fee58_100_21316 :
    PopulationFees20258.bill (n:=21316) (PopulationFees20258.tabulate (21316-1) 256) source100.plan.table+
      4*21316*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*263824446871 := by decide +kernel
private theorem range58From20953To3159 : Segment 58 20953 21316 2812 3159 :=
  paid (pc:=70) (v:=263824446871) (by decide) source100_valid tests58_100_2812 fee58_100_21316 (by decide +kernel)

private theorem tests58_096_3159 : ∀ z∈source096.plan.table,z.1.Valid 58 3159 := by decide +kernel
private theorem fee58_096_21316 :
    PopulationFees20258.bill (n:=21316) (PopulationFees20258.tabulate (21316-1) 256) source096.plan.table+
      4*21316*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*230772173886 := by decide +kernel
private theorem range58From20953To3307 : Segment 58 20953 21316 3159 3307 :=
  paid (pc:=68) (v:=230772173886) (by decide) source096_valid tests58_096_3159 fee58_096_21316 (by decide +kernel)

private theorem range58From20953 : Win 58 20953 21316 :=
  complete (by decide) (by decide) (join_population (join_population range58From20953To2704 range58From20953To2808) (join_population range58From20953To2812 (join_population range58From20953To3159 range58From20953To3307)))

private theorem fee58_098_21700 :
    PopulationFees20258.bill (n:=21700) (PopulationFees20258.tabulate (21700-1) 256) source098.plan.table+
      4*21700*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*196325843570 := by decide +kernel
private theorem range58From21317To2713 : Segment 58 21317 21700 0 2713 :=
  paid (pc:=75) (v:=196325843570) (by decide) source098_valid tests58_098_0 fee58_098_21700 (by decide +kernel)

private theorem tests58_094_2713 : ∀ z∈source094.plan.table,z.1.Valid 58 2713 := by decide +kernel
private theorem fee58_094_21700 :
    PopulationFees20258.bill (n:=21700) (PopulationFees20258.tabulate (21700-1) 256) source094.plan.table+
      4*21700*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*244969264146 := by decide +kernel
private theorem range58From21317To2808 : Segment 58 21317 21700 2713 2808 :=
  paid (pc:=74) (v:=244969264146) (by decide) source094_valid tests58_094_2713 fee58_094_21700 (by decide +kernel)

private theorem range58From21317To2812 : Segment 58 21317 21700 2808 2812 :=
  paid (pc:=74) (v:=244969264146) (by decide) source094_valid tests58_094_2808 fee58_094_21700 (by decide +kernel)

private theorem fee58_100_21700 :
    PopulationFees20258.bill (n:=21700) (PopulationFees20258.tabulate (21700-1) 256) source100.plan.table+
      4*21700*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*272359615627 := by decide +kernel
private theorem range58From21317To3128 : Segment 58 21317 21700 2812 3128 :=
  paid (pc:=71) (v:=272359615627) (by decide) source100_valid tests58_100_2812 fee58_100_21700 (by decide +kernel)

private theorem tests58_096_3128 : ∀ z∈source096.plan.table,z.1.Valid 58 3128 := by decide +kernel
private theorem fee58_096_21700 :
    PopulationFees20258.bill (n:=21700) (PopulationFees20258.tabulate (21700-1) 256) source096.plan.table+
      4*21700*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*238420721423 := by decide +kernel
private theorem range58From21317To3307 : Segment 58 21317 21700 3128 3307 :=
  paid (pc:=69) (v:=238420721423) (by decide) source096_valid tests58_096_3128 fee58_096_21700 (by decide +kernel)

private theorem range58From21317 : Win 58 21317 21700 :=
  complete (by decide) (by decide) (join_population (join_population range58From21317To2713 range58From21317To2808) (join_population range58From21317To2812 (join_population range58From21317To3128 range58From21317To3307)))

theorem cut58From20258 : Win 58 20258 21700 :=
  (join_ground (join_ground range58From20258 range58From20602) (join_ground range58From20953 range58From21317))

end JSP233.FiniteCutRanges20258
