module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source109
public import Erdos272.Arithmetic.N20258.Sources.Source110
public import Erdos272.Arithmetic.N20258.Sources.Source112

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests62_110_0 : ∀ z∈source110.plan.table,z.1.Valid 62 0 := by decide +kernel
private theorem fee62_110_21080 :
    PopulationFees20258.bill (n:=21080) (PopulationFees20258.tabulate (21080-1) 256) source110.plan.table+
      4*21080*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*175697967491 := by decide +kernel
private theorem range62From20258To3036 : Segment 62 20258 21080 0 3036 :=
  paid (pc:=68) (v:=175697967491) (by decide) source110_valid tests62_110_0 fee62_110_21080 (by decide +kernel)

private theorem tests62_110_3036 : ∀ z∈source110.plan.table,z.1.Valid 62 3036 := by decide +kernel
private theorem range62From20258To3081 : Segment 62 20258 21080 3036 3081 :=
  paid (pc:=67) (v:=175697967491) (by decide) source110_valid tests62_110_3036 fee62_110_21080 (by decide +kernel)

private theorem tests62_110_3081 : ∀ z∈source110.plan.table,z.1.Valid 62 3081 := by decide +kernel
private theorem range62From20258To3083 : Segment 62 20258 21080 3081 3083 :=
  paid (pc:=67) (v:=175697967491) (by decide) source110_valid tests62_110_3081 fee62_110_21080 (by decide +kernel)

private theorem tests62_102_3083 : ∀ z∈source102.plan.table,z.1.Valid 62 3083 := by decide +kernel
private theorem fee62_102_21080 :
    PopulationFees20258.bill (n:=21080) (PopulationFees20258.tabulate (21080-1) 256) source102.plan.table+
      4*21080*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*235250958267 := by decide +kernel
private theorem range62From20258To3146 : Segment 62 20258 21080 3083 3146 :=
  paid (pc:=67) (v:=235250958267) (by decide) source102_valid tests62_102_3083 fee62_102_21080 (by decide +kernel)

private theorem tests62_106_3146 : ∀ z∈source106.plan.table,z.1.Valid 62 3146 := by decide +kernel
private theorem fee62_106_21080 :
    PopulationFees20258.bill (n:=21080) (PopulationFees20258.tabulate (21080-1) 256) source106.plan.table+
      4*21080*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*268971387610 := by decide +kernel
private theorem range62From20258To3783 : Segment 62 20258 21080 3146 3783 :=
  paid (pc:=60) (v:=268971387610) (by decide) source106_valid tests62_106_3146 fee62_106_21080 (by decide +kernel)

private theorem range62From20258 : Win 62 20258 21080 :=
  complete (by decide) (by decide) (join_population (join_population range62From20258To3036 range62From20258To3081) (join_population range62From20258To3083 (join_population range62From20258To3146 range62From20258To3783)))

private theorem fee62_110_21843 :
    PopulationFees20258.bill (n:=21843) (PopulationFees20258.tabulate (21843-1) 256) source110.plan.table+
      4*21843*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*187466039851 := by decide +kernel
private theorem range62From21081To3048 : Segment 62 21081 21843 0 3048 :=
  paid (pc:=69) (v:=187466039851) (by decide) source110_valid tests62_110_0 fee62_110_21843 (by decide +kernel)

private theorem tests62_110_3048 : ∀ z∈source110.plan.table,z.1.Valid 62 3048 := by decide +kernel
private theorem range62From21081To3087 : Segment 62 21081 21843 3048 3087 :=
  paid (pc:=69) (v:=187466039851) (by decide) source110_valid tests62_110_3048 fee62_110_21843 (by decide +kernel)

private theorem tests62_102_3087 : ∀ z∈source102.plan.table,z.1.Valid 62 3087 := by decide +kernel
private theorem fee62_102_21843 :
    PopulationFees20258.bill (n:=21843) (PopulationFees20258.tabulate (21843-1) 256) source102.plan.table+
      4*21843*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*251011334290 := by decide +kernel
private theorem range62From21081To3118 : Segment 62 21081 21843 3087 3118 :=
  paid (pc:=69) (v:=251011334290) (by decide) source102_valid tests62_102_3087 fee62_102_21843 (by decide +kernel)

private theorem tests62_102_3118 : ∀ z∈source102.plan.table,z.1.Valid 62 3118 := by decide +kernel
private theorem range62From21081To3120 : Segment 62 21081 21843 3118 3120 :=
  paid (pc:=69) (v:=251011334290) (by decide) source102_valid tests62_102_3118 fee62_102_21843 (by decide +kernel)

private theorem tests62_106_3120 : ∀ z∈source106.plan.table,z.1.Valid 62 3120 := by decide +kernel
private theorem fee62_106_21843 :
    PopulationFees20258.bill (n:=21843) (PopulationFees20258.tabulate (21843-1) 256) source106.plan.table+
      4*21843*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*286702651953 := by decide +kernel
private theorem range62From21081To3714 : Segment 62 21081 21843 3120 3714 :=
  paid (pc:=63) (v:=286702651953) (by decide) source106_valid tests62_106_3120 fee62_106_21843 (by decide +kernel)

private theorem tests62_112_3714 : ∀ z∈source112.plan.table,z.1.Valid 62 3714 := by decide +kernel
private theorem fee62_112_21843 :
    PopulationFees20258.bill (n:=21843) (PopulationFees20258.tabulate (21843-1) 256) source112.plan.table+
      4*21843*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*241795565128 := by decide +kernel
private theorem range62From21081To3783 : Segment 62 21081 21843 3714 3783 :=
  paid (pc:=59) (v:=241795565128) (by decide) source112_valid tests62_112_3714 fee62_112_21843 (by decide +kernel)

private theorem range62From21081 : Win 62 21081 21843 :=
  complete (by decide) (by decide) (join_population (join_population range62From21081To3048 (join_population range62From21081To3087 range62From21081To3118)) (join_population range62From21081To3120 (join_population range62From21081To3714 range62From21081To3783)))

private theorem fee62_110_22570 :
    PopulationFees20258.bill (n:=22570) (PopulationFees20258.tabulate (22570-1) 256) source110.plan.table+
      4*22570*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*198882839470 := by decide +kernel
private theorem range62From21844To3069 : Segment 62 21844 22570 0 3069 :=
  paid (pc:=70) (v:=198882839470) (by decide) source110_valid tests62_110_0 fee62_110_22570 (by decide +kernel)

private theorem tests62_110_3069 : ∀ z∈source110.plan.table,z.1.Valid 62 3069 := by decide +kernel
private theorem range62From21844To3104 : Segment 62 21844 22570 3069 3104 :=
  paid (pc:=70) (v:=198882839470) (by decide) source110_valid tests62_110_3069 fee62_110_22570 (by decide +kernel)

private theorem tests62_102_3104 : ∀ z∈source102.plan.table,z.1.Valid 62 3104 := by decide +kernel
private theorem fee62_102_22570 :
    PopulationFees20258.bill (n:=22570) (PopulationFees20258.tabulate (22570-1) 256) source102.plan.table+
      4*22570*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*266108026464 := by decide +kernel
private theorem range62From21844To3118 : Segment 62 21844 22570 3104 3118 :=
  paid (pc:=70) (v:=266108026464) (by decide) source102_valid tests62_102_3104 fee62_102_22570 (by decide +kernel)

private theorem range62From21844To3120 : Segment 62 21844 22570 3118 3120 :=
  paid (pc:=70) (v:=266108026464) (by decide) source102_valid tests62_102_3118 fee62_102_22570 (by decide +kernel)

private theorem fee62_106_22570 :
    PopulationFees20258.bill (n:=22570) (PopulationFees20258.tabulate (22570-1) 256) source106.plan.table+
      4*22570*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*304063338223 := by decide +kernel
private theorem range62From21844To3524 : Segment 62 21844 22570 3120 3524 :=
  paid (pc:=66) (v:=304063338223) (by decide) source106_valid tests62_106_3120 fee62_106_22570 (by decide +kernel)

private theorem tests62_109_3524 : ∀ z∈source109.plan.table,z.1.Valid 62 3524 := by decide +kernel
private theorem fee62_109_22570 :
    PopulationFees20258.bill (n:=22570) (PopulationFees20258.tabulate (22570-1) 256) source109.plan.table+
      4*22570*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*242659809464 := by decide +kernel
private theorem range62From21844To3783 : Segment 62 21844 22570 3524 3783 :=
  paid (pc:=63) (v:=242659809464) (by decide) source109_valid tests62_109_3524 fee62_109_22570 (by decide +kernel)

private theorem range62From21844 : Win 62 21844 22570 :=
  complete (by decide) (by decide) (join_population (join_population range62From21844To3069 (join_population range62From21844To3104 range62From21844To3118)) (join_population range62From21844To3120 (join_population range62From21844To3524 range62From21844To3783)))

private theorem fee62_110_23288 :
    PopulationFees20258.bill (n:=23288) (PopulationFees20258.tabulate (23288-1) 256) source110.plan.table+
      4*23288*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*210574208603 := by decide +kernel
private theorem range62From22571To3087 : Segment 62 22571 23288 0 3087 :=
  paid (pc:=71) (v:=210574208603) (by decide) source110_valid tests62_110_0 fee62_110_23288 (by decide +kernel)

private theorem tests62_110_3087 : ∀ z∈source110.plan.table,z.1.Valid 62 3087 := by decide +kernel
private theorem range62From22571To3118 : Segment 62 22571 23288 3087 3118 :=
  paid (pc:=71) (v:=210574208603) (by decide) source110_valid tests62_110_3087 fee62_110_23288 (by decide +kernel)

private theorem fee62_102_23288 :
    PopulationFees20258.bill (n:=23288) (PopulationFees20258.tabulate (23288-1) 256) source102.plan.table+
      4*23288*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*281762914603 := by decide +kernel
private theorem range62From22571To3120 : Segment 62 22571 23288 3118 3120 :=
  paid (pc:=71) (v:=281762914603) (by decide) source102_valid tests62_102_3118 fee62_102_23288 (by decide +kernel)

private theorem fee62_106_23288 :
    PopulationFees20258.bill (n:=23288) (PopulationFees20258.tabulate (23288-1) 256) source106.plan.table+
      4*23288*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*321623393190 := by decide +kernel
private theorem range62From22571To3437 : Segment 62 22571 23288 3120 3437 :=
  paid (pc:=68) (v:=321623393190) (by decide) source106_valid tests62_106_3120 fee62_106_23288 (by decide +kernel)

private theorem tests62_105_3437 : ∀ z∈source105.plan.table,z.1.Valid 62 3437 := by decide +kernel
private theorem fee62_105_23288 :
    PopulationFees20258.bill (n:=23288) (PopulationFees20258.tabulate (23288-1) 256) source105.plan.table+
      4*23288*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*315304413914 := by decide +kernel
private theorem range62From22571To3522 : Segment 62 22571 23288 3437 3522 :=
  paid (pc:=68) (v:=315304413914) (by decide) source105_valid tests62_105_3437 fee62_105_23288 (by decide +kernel)

private theorem tests62_109_3522 : ∀ z∈source109.plan.table,z.1.Valid 62 3522 := by decide +kernel
private theorem fee62_109_23288 :
    PopulationFees20258.bill (n:=23288) (PopulationFees20258.tabulate (23288-1) 256) source109.plan.table+
      4*23288*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*257060892398 := by decide +kernel
private theorem range62From22571To3783 : Segment 62 22571 23288 3522 3783 :=
  paid (pc:=64) (v:=257060892398) (by decide) source109_valid tests62_109_3522 fee62_109_23288 (by decide +kernel)

private theorem range62From22571 : Win 62 22571 23288 :=
  complete (by decide) (by decide) (join_population (join_population range62From22571To3087 (join_population range62From22571To3118 range62From22571To3120)) (join_population range62From22571To3437 (join_population range62From22571To3522 range62From22571To3783)))

theorem cut62From20258 : Win 62 20258 23288 :=
  (join_ground (join_ground range62From20258 range62From21081) (join_ground range62From21844 range62From22571))

end JSP233.FiniteCutRanges20258
