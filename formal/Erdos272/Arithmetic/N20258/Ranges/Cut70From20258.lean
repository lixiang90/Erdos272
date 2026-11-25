module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source119
public import Erdos272.Arithmetic.N20258.Sources.Source121
public import Erdos272.Arithmetic.N20258.Sources.Source122

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests70_121_0 : ∀ z∈source121.plan.table,z.1.Valid 70 0 := by decide +kernel
private theorem fee70_121_24312 :
    PopulationFees20258.bill (n:=24312) (PopulationFees20258.tabulate (24312-1) 256) source121.plan.table+
      4*24312*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*260192223504 := by decide +kernel
private theorem range70From20258To2530 : Segment 70 20258 24312 0 2530 :=
  paid (pc:=57) (v:=260192223504) (by decide) source121_valid tests70_121_0 fee70_121_24312 (by decide +kernel)

private theorem tests70_121_2530 : ∀ z∈source121.plan.table,z.1.Valid 70 2530 := by decide +kernel
private theorem range70From20258To2698 : Segment 70 20258 24312 2530 2698 :=
  paid (pc:=55) (v:=260192223504) (by decide) source121_valid tests70_121_2530 fee70_121_24312 (by decide +kernel)

private theorem tests70_121_2698 : ∀ z∈source121.plan.table,z.1.Valid 70 2698 := by decide +kernel
private theorem range70From20258To2779 : Segment 70 20258 24312 2698 2779 :=
  paid (pc:=54) (v:=260192223504) (by decide) source121_valid tests70_121_2698 fee70_121_24312 (by decide +kernel)

private theorem tests70_121_2779 : ∀ z∈source121.plan.table,z.1.Valid 70 2779 := by decide +kernel
private theorem range70From20258To4831 : Segment 70 20258 24312 2779 4831 :=
  paid (pc:=53) (v:=260192223504) (by decide) source121_valid tests70_121_2779 fee70_121_24312 (by decide +kernel)

private theorem range70From20258 : Win 70 20258 24312 :=
  complete (by decide) (by decide) (join_population (join_population range70From20258To2530 range70From20258To2698) (join_population range70From20258To2779 range70From20258To4831))

private theorem fee70_121_26700 :
    PopulationFees20258.bill (n:=26700) (PopulationFees20258.tabulate (26700-1) 256) source121.plan.table+
      4*26700*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*308567379637 := by decide +kernel
private theorem range70From24313To3709 : Segment 70 24313 26700 0 3709 :=
  paid (pc:=61) (v:=308567379637) (by decide) source121_valid tests70_121_0 fee70_121_26700 (by decide +kernel)

private theorem tests70_121_3709 : ∀ z∈source121.plan.table,z.1.Valid 70 3709 := by decide +kernel
private theorem range70From24313To3787 : Segment 70 24313 26700 3709 3787 :=
  paid (pc:=60) (v:=308567379637) (by decide) source121_valid tests70_121_3709 fee70_121_26700 (by decide +kernel)

private theorem tests70_121_3787 : ∀ z∈source121.plan.table,z.1.Valid 70 3787 := by decide +kernel
private theorem range70From24313To3791 : Segment 70 24313 26700 3787 3791 :=
  paid (pc:=60) (v:=308567379637) (by decide) source121_valid tests70_121_3787 fee70_121_26700 (by decide +kernel)

private theorem tests70_119_3791 : ∀ z∈source119.plan.table,z.1.Valid 70 3791 := by decide +kernel
private theorem fee70_119_26700 :
    PopulationFees20258.bill (n:=26700) (PopulationFees20258.tabulate (26700-1) 256) source119.plan.table+
      4*26700*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*785748961413 := by decide +kernel
private theorem range70From24313To4831 : Segment 70 24313 26700 3791 4831 :=
  paid (pc:=71) (v:=785748961413) (by decide) source119_valid tests70_119_3791 fee70_119_26700 (by decide +kernel)

private theorem range70From24313 : Win 70 24313 26700 :=
  complete (by decide) (by decide) (join_population (join_population range70From24313To3709 range70From24313To3787) (join_population range70From24313To3791 range70From24313To4831))

private theorem fee70_121_28770 :
    PopulationFees20258.bill (n:=28770) (PopulationFees20258.tabulate (28770-1) 256) source121.plan.table+
      4*28770*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*353952099148 := by decide +kernel
private theorem range70From26701To3747 : Segment 70 26701 28770 0 3747 :=
  paid (pc:=66) (v:=353952099148) (by decide) source121_valid tests70_121_0 fee70_121_28770 (by decide +kernel)

private theorem tests70_121_3747 : ∀ z∈source121.plan.table,z.1.Valid 70 3747 := by decide +kernel
private theorem range70From26701To3791 : Segment 70 26701 28770 3747 3791 :=
  paid (pc:=65) (v:=353952099148) (by decide) source121_valid tests70_121_3747 fee70_121_28770 (by decide +kernel)

private theorem fee70_119_28770 :
    PopulationFees20258.bill (n:=28770) (PopulationFees20258.tabulate (28770-1) 256) source119.plan.table+
      4*28770*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*897321207723 := by decide +kernel
private theorem range70From26701To4831 : Segment 70 26701 28770 3791 4831 :=
  paid (pc:=66) (v:=897321207723) (by decide) source119_valid tests70_119_3791 fee70_119_28770 (by decide +kernel)

private theorem range70From26701 : Win 70 26701 28770 :=
  complete (by decide) (by decide) (join_population range70From26701To3747 (join_population range70From26701To3791 range70From26701To4831))

private theorem fee70_121_30840 :
    PopulationFees20258.bill (n:=30840) (PopulationFees20258.tabulate (30840-1) 256) source121.plan.table+
      4*30840*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*402205624985 := by decide +kernel
private theorem range70From28771To3759 : Segment 70 28771 30840 0 3759 :=
  paid (pc:=68) (v:=402205624985) (by decide) source121_valid tests70_121_0 fee70_121_30840 (by decide +kernel)

private theorem tests70_121_3759 : ∀ z∈source121.plan.table,z.1.Valid 70 3759 := by decide +kernel
private theorem range70From28771To3791 : Segment 70 28771 30840 3759 3791 :=
  paid (pc:=68) (v:=402205624985) (by decide) source121_valid tests70_121_3759 fee70_121_30840 (by decide +kernel)

private theorem fee70_119_30840 :
    PopulationFees20258.bill (n:=30840) (PopulationFees20258.tabulate (30840-1) 256) source119.plan.table+
      4*30840*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1015687880893 := by decide +kernel
private theorem range70From28771To4831 : Segment 70 28771 30840 3791 4831 :=
  paid (pc:=61) (v:=1015687880893) (by decide) source119_valid tests70_119_3791 fee70_119_30840 (by decide +kernel)

private theorem range70From28771 : Win 70 28771 30840 :=
  complete (by decide) (by decide) (join_population range70From28771To3759 (join_population range70From28771To3791 range70From28771To4831))

private theorem fee70_121_33076 :
    PopulationFees20258.bill (n:=33076) (PopulationFees20258.tabulate (33076-1) 256) source121.plan.table+
      4*33076*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*457927121119 := by decide +kernel
private theorem range70From30841To3767 : Segment 70 30841 33076 0 3767 :=
  paid (pc:=70) (v:=457927121119) (by decide) source121_valid tests70_121_0 fee70_121_33076 (by decide +kernel)

private theorem tests70_121_3767 : ∀ z∈source121.plan.table,z.1.Valid 70 3767 := by decide +kernel
private theorem range70From30841To3791 : Segment 70 30841 33076 3767 3791 :=
  paid (pc:=69) (v:=457927121119) (by decide) source121_valid tests70_121_3767 fee70_121_33076 (by decide +kernel)

private theorem fee70_119_33076 :
    PopulationFees20258.bill (n:=33076) (PopulationFees20258.tabulate (33076-1) 256) source119.plan.table+
      4*33076*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1151774138399 := by decide +kernel
private theorem range70From30841To4166 : Segment 70 30841 33076 3791 4166 :=
  paid (pc:=67) (v:=1151774138399) (by decide) source119_valid tests70_119_3791 fee70_119_33076 (by decide +kernel)

private theorem tests70_122_4166 : ∀ z∈source122.plan.table,z.1.Valid 70 4166 := by decide +kernel
private theorem fee70_122_33076 :
    PopulationFees20258.bill (n:=33076) (PopulationFees20258.tabulate (33076-1) 256) source122.plan.table+
      4*33076*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*884158830291 := by decide +kernel
private theorem range70From30841To4831 : Segment 70 30841 33076 4166 4831 :=
  paid (pc:=61) (v:=884158830291) (by decide) source122_valid tests70_122_4166 fee70_122_33076 (by decide +kernel)

private theorem range70From30841 : Win 70 30841 33076 :=
  complete (by decide) (by decide) (join_population (join_population range70From30841To3767 range70From30841To3791) (join_population range70From30841To4166 range70From30841To4831))

private theorem fee70_121_35341 :
    PopulationFees20258.bill (n:=35341) (PopulationFees20258.tabulate (35341-1) 256) source121.plan.table+
      4*35341*NaturalPopulation20258.weights source121.extras≤source121.plan.scale*517980027631 := by decide +kernel
private theorem range70From33077To3886 : Segment 70 33077 35341 0 3886 :=
  paid (pc:=71) (v:=517980027631) (by decide) source121_valid tests70_121_0 fee70_121_35341 (by decide +kernel)

private theorem tests70_119_3886 : ∀ z∈source119.plan.table,z.1.Valid 70 3886 := by decide +kernel
private theorem fee70_119_35341 :
    PopulationFees20258.bill (n:=35341) (PopulationFees20258.tabulate (35341-1) 256) source119.plan.table+
      4*35341*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1298115619811 := by decide +kernel
private theorem range70From33077To4066 : Segment 70 33077 35341 3886 4066 :=
  paid (pc:=70) (v:=1298115619811) (by decide) source119_valid tests70_119_3886 fee70_119_35341 (by decide +kernel)

private theorem tests70_119_4066 : ∀ z∈source119.plan.table,z.1.Valid 70 4066 := by decide +kernel
private theorem range70From33077To4072 : Segment 70 33077 35341 4066 4072 :=
  paid (pc:=70) (v:=1298115619811) (by decide) source119_valid tests70_119_4066 fee70_119_35341 (by decide +kernel)

private theorem tests70_119_4072 : ∀ z∈source119.plan.table,z.1.Valid 70 4072 := by decide +kernel
private theorem range70From33077To4075 : Segment 70 33077 35341 4072 4075 :=
  paid (pc:=70) (v:=1298115619811) (by decide) source119_valid tests70_119_4072 fee70_119_35341 (by decide +kernel)

private theorem tests70_122_4075 : ∀ z∈source122.plan.table,z.1.Valid 70 4075 := by decide +kernel
private theorem fee70_122_35341 :
    PopulationFees20258.bill (n:=35341) (PopulationFees20258.tabulate (35341-1) 256) source122.plan.table+
      4*35341*NaturalPopulation20258.weights source122.extras≤source122.plan.scale*996048250299 := by decide +kernel
private theorem range70From33077To4831 : Segment 70 33077 35341 4075 4831 :=
  paid (pc:=64) (v:=996048250299) (by decide) source122_valid tests70_122_4075 fee70_122_35341 (by decide +kernel)

private theorem range70From33077 : Win 70 33077 35341 :=
  complete (by decide) (by decide) (join_population (join_population range70From33077To3886 range70From33077To4066) (join_population range70From33077To4072 (join_population range70From33077To4075 range70From33077To4831)))

theorem cut70From20258 : Win 70 20258 35341 :=
  (join_ground (join_ground range70From20258 (join_ground range70From24313 range70From26701)) (join_ground range70From28771 (join_ground range70From30841 range70From33077)))

end JSP233.FiniteCutRanges20258
