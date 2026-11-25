module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source101

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests59_101_0 : ∀ z∈source101.plan.table,z.1.Valid 59 0 := by decide +kernel
private theorem fee59_101_20524 :
    PopulationFees20258.bill (n:=20524) (PopulationFees20258.tabulate (20524-1) 256) source101.plan.table+
      4*20524*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*165522242814 := by decide +kernel
private theorem range59From20258To2815 : Segment 59 20258 20524 0 2815 :=
  paid (pc:=73) (v:=165522242814) (by decide) source101_valid tests59_101_0 fee59_101_20524 (by decide +kernel)

private theorem tests59_094_2815 : ∀ z∈source094.plan.table,z.1.Valid 59 2815 := by decide +kernel
private theorem fee59_094_20524 :
    PopulationFees20258.bill (n:=20524) (PopulationFees20258.tabulate (20524-1) 256) source094.plan.table+
      4*20524*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*221629660153 := by decide +kernel
private theorem range59From20258To2856 : Segment 59 20258 20524 2815 2856 :=
  paid (pc:=73) (v:=221629660153) (by decide) source094_valid tests59_094_2815 fee59_094_20524 (by decide +kernel)

private theorem tests59_094_2856 : ∀ z∈source094.plan.table,z.1.Valid 59 2856 := by decide +kernel
private theorem range59From20258To2858 : Segment 59 20258 20524 2856 2858 :=
  paid (pc:=73) (v:=221629660153) (by decide) source094_valid tests59_094_2856 fee59_094_20524 (by decide +kernel)

private theorem tests59_100_2858 : ∀ z∈source100.plan.table,z.1.Valid 59 2858 := by decide +kernel
private theorem fee59_100_20524 :
    PopulationFees20258.bill (n:=20524) (PopulationFees20258.tabulate (20524-1) 256) source100.plan.table+
      4*20524*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*246468499266 := by decide +kernel
private theorem range59From20258To3315 : Segment 59 20258 20524 2858 3315 :=
  paid (pc:=68) (v:=246468499266) (by decide) source100_valid tests59_100_2858 fee59_100_20524 (by decide +kernel)

private theorem tests59_096_3315 : ∀ z∈source096.plan.table,z.1.Valid 59 3315 := by decide +kernel
private theorem fee59_096_20524 :
    PopulationFees20258.bill (n:=20524) (PopulationFees20258.tabulate (20524-1) 256) source096.plan.table+
      4*20524*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*215580663627 := by decide +kernel
private theorem range59From20258To3423 : Segment 59 20258 20524 3315 3423 :=
  paid (pc:=66) (v:=215580663627) (by decide) source096_valid tests59_096_3315 fee59_096_20524 (by decide +kernel)

private theorem range59From20258 : Win 59 20258 20524 :=
  complete (by decide) (by decide) (join_population (join_population range59From20258To2815 range59From20258To2856) (join_population range59From20258To2858 (join_population range59From20258To3315 range59From20258To3423)))

private theorem fee59_101_20794 :
    PopulationFees20258.bill (n:=20794) (PopulationFees20258.tabulate (20794-1) 256) source101.plan.table+
      4*20794*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*169489494173 := by decide +kernel
private theorem range59From20525To2821 : Segment 59 20525 20794 0 2821 :=
  paid (pc:=73) (v:=169489494173) (by decide) source101_valid tests59_101_0 fee59_101_20794 (by decide +kernel)

private theorem tests59_094_2821 : ∀ z∈source094.plan.table,z.1.Valid 59 2821 := by decide +kernel
private theorem fee59_094_20794 :
    PopulationFees20258.bill (n:=20794) (PopulationFees20258.tabulate (20794-1) 256) source094.plan.table+
      4*20794*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*226852664691 := by decide +kernel
private theorem range59From20525To2856 : Segment 59 20525 20794 2821 2856 :=
  paid (pc:=73) (v:=226852664691) (by decide) source094_valid tests59_094_2821 fee59_094_20794 (by decide +kernel)

private theorem range59From20525To2858 : Segment 59 20525 20794 2856 2858 :=
  paid (pc:=73) (v:=226852664691) (by decide) source094_valid tests59_094_2856 fee59_094_20794 (by decide +kernel)

private theorem fee59_100_20794 :
    PopulationFees20258.bill (n:=20794) (PopulationFees20258.tabulate (20794-1) 256) source100.plan.table+
      4*20794*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*252386884935 := by decide +kernel
private theorem range59From20525To3272 : Segment 59 20525 20794 2858 3272 :=
  paid (pc:=69) (v:=252386884935) (by decide) source100_valid tests59_100_2858 fee59_100_20794 (by decide +kernel)

private theorem tests59_096_3272 : ∀ z∈source096.plan.table,z.1.Valid 59 3272 := by decide +kernel
private theorem fee59_096_20794 :
    PopulationFees20258.bill (n:=20794) (PopulationFees20258.tabulate (20794-1) 256) source096.plan.table+
      4*20794*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*220688292097 := by decide +kernel
private theorem range59From20525To3423 : Segment 59 20525 20794 3272 3423 :=
  paid (pc:=67) (v:=220688292097) (by decide) source096_valid tests59_096_3272 fee59_096_20794 (by decide +kernel)

private theorem range59From20525 : Win 59 20525 20794 :=
  complete (by decide) (by decide) (join_population (join_population range59From20525To2821 range59From20525To2856) (join_population range59From20525To2858 (join_population range59From20525To3272 range59From20525To3423)))

private theorem fee59_101_21069 :
    PopulationFees20258.bill (n:=21069) (PopulationFees20258.tabulate (21069-1) 256) source101.plan.table+
      4*21069*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*173524628199 := by decide +kernel
private theorem range59From20795To2827 : Segment 59 20795 21069 0 2827 :=
  paid (pc:=74) (v:=173524628199) (by decide) source101_valid tests59_101_0 fee59_101_21069 (by decide +kernel)

private theorem tests59_094_2827 : ∀ z∈source094.plan.table,z.1.Valid 59 2827 := by decide +kernel
private theorem fee59_094_21069 :
    PopulationFees20258.bill (n:=21069) (PopulationFees20258.tabulate (21069-1) 256) source094.plan.table+
      4*21069*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*232316571571 := by decide +kernel
private theorem range59From20795To2856 : Segment 59 20795 21069 2827 2856 :=
  paid (pc:=73) (v:=232316571571) (by decide) source094_valid tests59_094_2827 fee59_094_21069 (by decide +kernel)

private theorem range59From20795To2858 : Segment 59 20795 21069 2856 2858 :=
  paid (pc:=73) (v:=232316571571) (by decide) source094_valid tests59_094_2856 fee59_094_21069 (by decide +kernel)

private theorem fee59_100_21069 :
    PopulationFees20258.bill (n:=21069) (PopulationFees20258.tabulate (21069-1) 256) source100.plan.table+
      4*21069*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*258347143893 := by decide +kernel
private theorem range59From20795To3240 : Segment 59 20795 21069 2858 3240 :=
  paid (pc:=70) (v:=258347143893) (by decide) source100_valid tests59_100_2858 fee59_100_21069 (by decide +kernel)

private theorem tests59_096_3240 : ∀ z∈source096.plan.table,z.1.Valid 59 3240 := by decide +kernel
private theorem fee59_096_21069 :
    PopulationFees20258.bill (n:=21069) (PopulationFees20258.tabulate (21069-1) 256) source096.plan.table+
      4*21069*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*226041982936 := by decide +kernel
private theorem range59From20795To3423 : Segment 59 20795 21069 3240 3423 :=
  paid (pc:=68) (v:=226041982936) (by decide) source096_valid tests59_096_3240 fee59_096_21069 (by decide +kernel)

private theorem range59From20795 : Win 59 20795 21069 :=
  complete (by decide) (by decide) (join_population (join_population range59From20795To2827 range59From20795To2856) (join_population range59From20795To2858 (join_population range59From20795To3240 range59From20795To3423)))

private theorem fee59_101_21360 :
    PopulationFees20258.bill (n:=21360) (PopulationFees20258.tabulate (21360-1) 256) source101.plan.table+
      4*21360*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*177944954316 := by decide +kernel
private theorem range59From21070To2830 : Segment 59 21070 21360 0 2830 :=
  paid (pc:=74) (v:=177944954316) (by decide) source101_valid tests59_101_0 fee59_101_21360 (by decide +kernel)

private theorem tests59_101_2830 : ∀ z∈source101.plan.table,z.1.Valid 59 2830 := by decide +kernel
private theorem range59From21070To2856 : Segment 59 21070 21360 2830 2856 :=
  paid (pc:=74) (v:=177944954316) (by decide) source101_valid tests59_101_2830 fee59_101_21360 (by decide +kernel)

private theorem tests59_101_2856 : ∀ z∈source101.plan.table,z.1.Valid 59 2856 := by decide +kernel
private theorem range59From21070To2858 : Segment 59 21070 21360 2856 2858 :=
  paid (pc:=74) (v:=177944954316) (by decide) source101_valid tests59_101_2856 fee59_101_21360 (by decide +kernel)

private theorem fee59_100_21360 :
    PopulationFees20258.bill (n:=21360) (PopulationFees20258.tabulate (21360-1) 256) source100.plan.table+
      4*21360*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*264746150067 := by decide +kernel
private theorem range59From21070To3207 : Segment 59 21070 21360 2858 3207 :=
  paid (pc:=70) (v:=264746150067) (by decide) source100_valid tests59_100_2858 fee59_100_21360 (by decide +kernel)

private theorem tests59_096_3207 : ∀ z∈source096.plan.table,z.1.Valid 59 3207 := by decide +kernel
private theorem fee59_096_21360 :
    PopulationFees20258.bill (n:=21360) (PopulationFees20258.tabulate (21360-1) 256) source096.plan.table+
      4*21360*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*231632103893 := by decide +kernel
private theorem range59From21070To3423 : Segment 59 21070 21360 3207 3423 :=
  paid (pc:=68) (v:=231632103893) (by decide) source096_valid tests59_096_3207 fee59_096_21360 (by decide +kernel)

private theorem range59From21070 : Win 59 21070 21360 :=
  complete (by decide) (by decide) (join_population (join_population range59From21070To2830 range59From21070To2856) (join_population range59From21070To2858 (join_population range59From21070To3207 range59From21070To3423)))

private theorem fee59_101_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source101.plan.table+
      4*21672*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*182683339136 := by decide +kernel
private theorem range59From21361To2833 : Segment 59 21361 21672 0 2833 :=
  paid (pc:=74) (v:=182683339136) (by decide) source101_valid tests59_101_0 fee59_101_21672 (by decide +kernel)

private theorem tests59_101_2833 : ∀ z∈source101.plan.table,z.1.Valid 59 2833 := by decide +kernel
private theorem range59From21361To2858 : Segment 59 21361 21672 2833 2858 :=
  paid (pc:=74) (v:=182683339136) (by decide) source101_valid tests59_101_2833 fee59_101_21672 (by decide +kernel)

private theorem fee59_100_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source100.plan.table+
      4*21672*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*271714715040 := by decide +kernel
private theorem range59From21361To3176 : Segment 59 21361 21672 2858 3176 :=
  paid (pc:=71) (v:=271714715040) (by decide) source100_valid tests59_100_2858 fee59_100_21672 (by decide +kernel)

private theorem tests59_096_3176 : ∀ z∈source096.plan.table,z.1.Valid 59 3176 := by decide +kernel
private theorem fee59_096_21672 :
    PopulationFees20258.bill (n:=21672) (PopulationFees20258.tabulate (21672-1) 256) source096.plan.table+
      4*21672*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*237874479932 := by decide +kernel
private theorem range59From21361To3423 : Segment 59 21361 21672 3176 3423 :=
  paid (pc:=68) (v:=237874479932) (by decide) source096_valid tests59_096_3176 fee59_096_21672 (by decide +kernel)

private theorem range59From21361 : Win 59 21361 21672 :=
  complete (by decide) (by decide) (join_population (join_population range59From21361To2833 range59From21361To2858) (join_population range59From21361To3176 range59From21361To3423))

theorem cut59From20258 : Win 59 20258 21672 :=
  (join_ground (join_ground range59From20258 range59From20525) (join_ground range59From20795 (join_ground range59From21070 range59From21361)))

end JSP233.FiniteCutRanges20258
