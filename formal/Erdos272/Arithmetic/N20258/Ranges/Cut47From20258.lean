module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source003
public import Erdos272.Arithmetic.N20258.Sources.Source004
public import Erdos272.Arithmetic.N20258.Sources.Source005
public import Erdos272.Arithmetic.N20258.Sources.Source006

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests47_003_0 : ∀ z∈source003.plan.table,z.1.Valid 47 0 := by decide +kernel
private theorem fee47_003_20610 :
    PopulationFees20258.bill (n:=20610) (PopulationFees20258.tabulate (20610-1) 256) source003.plan.table+
      4*20610*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*72947594960 := by decide +kernel
private theorem range47From20258To2014 : Segment 47 20258 20610 0 2014 :=
  paid (pc:=80) (v:=72947594960) (by decide) source003_valid tests47_003_0 fee47_003_20610 (by decide +kernel)

private theorem tests47_004_2014 : ∀ z∈source004.plan.table,z.1.Valid 47 2014 := by decide +kernel
private theorem fee47_004_20610 :
    PopulationFees20258.bill (n:=20610) (PopulationFees20258.tabulate (20610-1) 256) source004.plan.table+
      4*20610*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*136360742150 := by decide +kernel
private theorem range47From20258To2103 : Segment 47 20258 20610 2014 2103 :=
  paid (pc:=79) (v:=136360742150) (by decide) source004_valid tests47_004_2014 fee47_004_20610 (by decide +kernel)

private theorem tests47_004_2103 : ∀ z∈source004.plan.table,z.1.Valid 47 2103 := by decide +kernel
private theorem range47From20258To2105 : Segment 47 20258 20610 2103 2105 :=
  paid (pc:=79) (v:=136360742150) (by decide) source004_valid tests47_004_2103 fee47_004_20610 (by decide +kernel)

private theorem tests47_005_2105 : ∀ z∈source005.plan.table,z.1.Valid 47 2105 := by decide +kernel
private theorem fee47_005_20610 :
    PopulationFees20258.bill (n:=20610) (PopulationFees20258.tabulate (20610-1) 256) source005.plan.table+
      4*20610*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*170222098780 := by decide +kernel
private theorem range47From20258To2150 : Segment 47 20258 20610 2105 2150 :=
  paid (pc:=78) (v:=170222098780) (by decide) source005_valid tests47_005_2105 fee47_005_20610 (by decide +kernel)

private theorem tests47_005_2150 : ∀ z∈source005.plan.table,z.1.Valid 47 2150 := by decide +kernel
private theorem range47From20258To2151 : Segment 47 20258 20610 2150 2151 :=
  paid (pc:=78) (v:=170222098780) (by decide) source005_valid tests47_005_2150 fee47_005_20610 (by decide +kernel)

private theorem tests47_006_2151 : ∀ z∈source006.plan.table,z.1.Valid 47 2151 := by decide +kernel
private theorem fee47_006_20610 :
    PopulationFees20258.bill (n:=20610) (PopulationFees20258.tabulate (20610-1) 256) source006.plan.table+
      4*20610*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*163257520854 := by decide +kernel
private theorem range47From20258To2163 : Segment 47 20258 20610 2151 2163 :=
  paid (pc:=78) (v:=163257520854) (by decide) source006_valid tests47_006_2151 fee47_006_20610 (by decide +kernel)

private theorem range47From20258 : Win 47 20258 20610 :=
  complete (by decide) (by decide) (join_population (join_population range47From20258To2014 (join_population range47From20258To2103 range47From20258To2105)) (join_population range47From20258To2150 (join_population range47From20258To2151 range47From20258To2163)))

private theorem fee47_003_21048 :
    PopulationFees20258.bill (n:=21048) (PopulationFees20258.tabulate (21048-1) 256) source003.plan.table+
      4*21048*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*75916240495 := by decide +kernel
private theorem range47From20611To2025 : Segment 47 20611 21048 0 2025 :=
  paid (pc:=79) (v:=75916240495) (by decide) source003_valid tests47_003_0 fee47_003_21048 (by decide +kernel)

private theorem tests47_004_2025 : ∀ z∈source004.plan.table,z.1.Valid 47 2025 := by decide +kernel
private theorem fee47_004_21048 :
    PopulationFees20258.bill (n:=21048) (PopulationFees20258.tabulate (21048-1) 256) source004.plan.table+
      4*21048*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*141809771735 := by decide +kernel
private theorem range47From20611To2108 : Segment 47 20611 21048 2025 2108 :=
  paid (pc:=79) (v:=141809771735) (by decide) source004_valid tests47_004_2025 fee47_004_21048 (by decide +kernel)

private theorem tests47_005_2108 : ∀ z∈source005.plan.table,z.1.Valid 47 2108 := by decide +kernel
private theorem fee47_005_21048 :
    PopulationFees20258.bill (n:=21048) (PopulationFees20258.tabulate (21048-1) 256) source005.plan.table+
      4*21048*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*176986159322 := by decide +kernel
private theorem range47From20611To2150 : Segment 47 20611 21048 2108 2150 :=
  paid (pc:=78) (v:=176986159322) (by decide) source005_valid tests47_005_2108 fee47_005_21048 (by decide +kernel)

private theorem range47From20611To2151 : Segment 47 20611 21048 2150 2151 :=
  paid (pc:=78) (v:=176986159322) (by decide) source005_valid tests47_005_2150 fee47_005_21048 (by decide +kernel)

private theorem fee47_006_21048 :
    PopulationFees20258.bill (n:=21048) (PopulationFees20258.tabulate (21048-1) 256) source006.plan.table+
      4*21048*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*169774161284 := by decide +kernel
private theorem range47From20611To2163 : Segment 47 20611 21048 2151 2163 :=
  paid (pc:=78) (v:=169774161284) (by decide) source006_valid tests47_006_2151 fee47_006_21048 (by decide +kernel)

private theorem range47From20611 : Win 47 20611 21048 :=
  complete (by decide) (by decide) (join_population (join_population range47From20611To2025 range47From20611To2108) (join_population range47From20611To2150 (join_population range47From20611To2151 range47From20611To2163)))

private theorem fee47_003_21596 :
    PopulationFees20258.bill (n:=21596) (PopulationFees20258.tabulate (21596-1) 256) source003.plan.table+
      4*21596*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*79693520305 := by decide +kernel
private theorem range47From21049To2037 : Segment 47 21049 21596 0 2037 :=
  paid (pc:=79) (v:=79693520305) (by decide) source003_valid tests47_003_0 fee47_003_21596 (by decide +kernel)

private theorem tests47_004_2037 : ∀ z∈source004.plan.table,z.1.Valid 47 2037 := by decide +kernel
private theorem fee47_004_21596 :
    PopulationFees20258.bill (n:=21596) (PopulationFees20258.tabulate (21596-1) 256) source004.plan.table+
      4*21596*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*148770592058 := by decide +kernel
private theorem range47From21049To2112 : Segment 47 21049 21596 2037 2112 :=
  paid (pc:=79) (v:=148770592058) (by decide) source004_valid tests47_004_2037 fee47_004_21596 (by decide +kernel)

private theorem tests47_005_2112 : ∀ z∈source005.plan.table,z.1.Valid 47 2112 := by decide +kernel
private theorem fee47_005_21596 :
    PopulationFees20258.bill (n:=21596) (PopulationFees20258.tabulate (21596-1) 256) source005.plan.table+
      4*21596*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*185621978239 := by decide +kernel
private theorem range47From21049To2150 : Segment 47 21049 21596 2112 2150 :=
  paid (pc:=78) (v:=185621978239) (by decide) source005_valid tests47_005_2112 fee47_005_21596 (by decide +kernel)

private theorem range47From21049To2151 : Segment 47 21049 21596 2150 2151 :=
  paid (pc:=78) (v:=185621978239) (by decide) source005_valid tests47_005_2150 fee47_005_21596 (by decide +kernel)

private theorem fee47_006_21596 :
    PopulationFees20258.bill (n:=21596) (PopulationFees20258.tabulate (21596-1) 256) source006.plan.table+
      4*21596*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*178073761422 := by decide +kernel
private theorem range47From21049To2163 : Segment 47 21049 21596 2151 2163 :=
  paid (pc:=78) (v:=178073761422) (by decide) source006_valid tests47_006_2151 fee47_006_21596 (by decide +kernel)

private theorem range47From21049 : Win 47 21049 21596 :=
  complete (by decide) (by decide) (join_population (join_population range47From21049To2037 range47From21049To2112) (join_population range47From21049To2150 (join_population range47From21049To2151 range47From21049To2163)))

private theorem fee47_003_22286 :
    PopulationFees20258.bill (n:=22286) (PopulationFees20258.tabulate (22286-1) 256) source003.plan.table+
      4*22286*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*84638799756 := by decide +kernel
private theorem range47From21597To2052 : Segment 47 21597 22286 0 2052 :=
  paid (pc:=79) (v:=84638799756) (by decide) source003_valid tests47_003_0 fee47_003_22286 (by decide +kernel)

private theorem tests47_004_2052 : ∀ z∈source004.plan.table,z.1.Valid 47 2052 := by decide +kernel
private theorem fee47_004_22286 :
    PopulationFees20258.bill (n:=22286) (PopulationFees20258.tabulate (22286-1) 256) source004.plan.table+
      4*22286*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*157861790608 := by decide +kernel
private theorem range47From21597To2118 : Segment 47 21597 22286 2052 2118 :=
  paid (pc:=78) (v:=157861790608) (by decide) source004_valid tests47_004_2052 fee47_004_22286 (by decide +kernel)

private theorem tests47_005_2118 : ∀ z∈source005.plan.table,z.1.Valid 47 2118 := by decide +kernel
private theorem fee47_005_22286 :
    PopulationFees20258.bill (n:=22286) (PopulationFees20258.tabulate (22286-1) 256) source005.plan.table+
      4*22286*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*196897436771 := by decide +kernel
private theorem range47From21597To2151 : Segment 47 21597 22286 2118 2151 :=
  paid (pc:=78) (v:=196897436771) (by decide) source005_valid tests47_005_2118 fee47_005_22286 (by decide +kernel)

private theorem fee47_006_22286 :
    PopulationFees20258.bill (n:=22286) (PopulationFees20258.tabulate (22286-1) 256) source006.plan.table+
      4*22286*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*188917691453 := by decide +kernel
private theorem range47From21597To2163 : Segment 47 21597 22286 2151 2163 :=
  paid (pc:=78) (v:=188917691453) (by decide) source006_valid tests47_006_2151 fee47_006_22286 (by decide +kernel)

private theorem range47From21597 : Win 47 21597 22286 :=
  complete (by decide) (by decide) (join_population (join_population range47From21597To2052 range47From21597To2118) (join_population range47From21597To2151 range47From21597To2163))

private theorem fee47_003_23166 :
    PopulationFees20258.bill (n:=23166) (PopulationFees20258.tabulate (23166-1) 256) source003.plan.table+
      4*23166*NaturalPopulation20258.weights source003.extras≤source003.plan.scale*91081156122 := by decide +kernel
private theorem range47From22287To2069 : Segment 47 22287 23166 0 2069 :=
  paid (pc:=78) (v:=91081156122) (by decide) source003_valid tests47_003_0 fee47_003_23166 (by decide +kernel)

private theorem tests47_004_2069 : ∀ z∈source004.plan.table,z.1.Valid 47 2069 := by decide +kernel
private theorem fee47_004_23166 :
    PopulationFees20258.bill (n:=23166) (PopulationFees20258.tabulate (23166-1) 256) source004.plan.table+
      4*23166*NaturalPopulation20258.weights source004.extras≤source004.plan.scale*169717873265 := by decide +kernel
private theorem range47From22287To2125 : Segment 47 22287 23166 2069 2125 :=
  paid (pc:=78) (v:=169717873265) (by decide) source004_valid tests47_004_2069 fee47_004_23166 (by decide +kernel)

private theorem tests47_005_2125 : ∀ z∈source005.plan.table,z.1.Valid 47 2125 := by decide +kernel
private theorem fee47_005_23166 :
    PopulationFees20258.bill (n:=23166) (PopulationFees20258.tabulate (23166-1) 256) source005.plan.table+
      4*23166*NaturalPopulation20258.weights source005.extras≤source005.plan.scale*211615972898 := by decide +kernel
private theorem range47From22287To2151 : Segment 47 22287 23166 2125 2151 :=
  paid (pc:=78) (v:=211615972898) (by decide) source005_valid tests47_005_2125 fee47_005_23166 (by decide +kernel)

private theorem fee47_006_23166 :
    PopulationFees20258.bill (n:=23166) (PopulationFees20258.tabulate (23166-1) 256) source006.plan.table+
      4*23166*NaturalPopulation20258.weights source006.extras≤source006.plan.scale*203071278857 := by decide +kernel
private theorem range47From22287To2163 : Segment 47 22287 23166 2151 2163 :=
  paid (pc:=78) (v:=203071278857) (by decide) source006_valid tests47_006_2151 fee47_006_23166 (by decide +kernel)

private theorem range47From22287 : Win 47 22287 23166 :=
  complete (by decide) (by decide) (join_population (join_population range47From22287To2069 range47From22287To2125) (join_population range47From22287To2151 range47From22287To2163))

theorem cut47From20258 : Win 47 20258 23166 :=
  (join_ground (join_ground range47From20258 range47From20611) (join_ground range47From21049 (join_ground range47From21597 range47From22287)))

end JSP233.FiniteCutRanges20258
