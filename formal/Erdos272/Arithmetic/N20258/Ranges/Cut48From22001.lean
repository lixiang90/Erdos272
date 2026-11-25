module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source007
public import Erdos272.Arithmetic.N20258.Sources.Source008
public import Erdos272.Arithmetic.N20258.Sources.Source009
public import Erdos272.Arithmetic.N20258.Sources.Source011
public import Erdos272.Arithmetic.N20258.Sources.Source012
public import Erdos272.Arithmetic.N20258.Sources.Source013

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests48_007_0 : ∀ z∈source007.plan.table,z.1.Valid 48 0 := by decide +kernel
private theorem fee48_007_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source007.plan.table+
      4*22736*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*80596971947 := by decide +kernel
private theorem range48From22001To2099 : Segment 48 22001 22736 0 2099 :=
  paid (pc:=79) (v:=80596971947) (by decide) source007_valid tests48_007_0 fee48_007_22736 (by decide +kernel)

private theorem tests48_008_2099 : ∀ z∈source008.plan.table,z.1.Valid 48 2099 := by decide +kernel
private theorem fee48_008_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source008.plan.table+
      4*22736*NaturalPopulation20258.weights source008.extras≤source008.plan.scale*159978626579 := by decide +kernel
private theorem range48From22001To2155 : Segment 48 22001 22736 2099 2155 :=
  paid (pc:=78) (v:=159978626579) (by decide) source008_valid tests48_008_2099 fee48_008_22736 (by decide +kernel)

private theorem tests48_009_2155 : ∀ z∈source009.plan.table,z.1.Valid 48 2155 := by decide +kernel
private theorem fee48_009_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source009.plan.table+
      4*22736*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*202412045259 := by decide +kernel
private theorem range48From22001To2178 : Segment 48 22001 22736 2155 2178 :=
  paid (pc:=78) (v:=202412045259) (by decide) source009_valid tests48_009_2155 fee48_009_22736 (by decide +kernel)

private theorem tests48_013_2178 : ∀ z∈source013.plan.table,z.1.Valid 48 2178 := by decide +kernel
private theorem fee48_013_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source013.plan.table+
      4*22736*NaturalPopulation20258.weights source013.extras≤source013.plan.scale*192766748355 := by decide +kernel
private theorem range48From22001To2219 : Segment 48 22001 22736 2178 2219 :=
  paid (pc:=78) (v:=192766748355) (by decide) source013_valid tests48_013_2178 fee48_013_22736 (by decide +kernel)

private theorem tests48_011_2219 : ∀ z∈source011.plan.table,z.1.Valid 48 2219 := by decide +kernel
private theorem fee48_011_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source011.plan.table+
      4*22736*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*187693076831 := by decide +kernel
private theorem range48From22001To2241 : Segment 48 22001 22736 2219 2241 :=
  paid (pc:=77) (v:=187693076831) (by decide) source011_valid tests48_011_2219 fee48_011_22736 (by decide +kernel)

private theorem tests48_012_2241 : ∀ z∈source012.plan.table,z.1.Valid 48 2241 := by decide +kernel
private theorem fee48_012_22736 :
    PopulationFees20258.bill (n:=22736) (PopulationFees20258.tabulate (22736-1) 256) source012.plan.table+
      4*22736*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*182653072376 := by decide +kernel
private theorem range48From22001To2257 : Segment 48 22001 22736 2241 2257 :=
  paid (pc:=77) (v:=182653072376) (by decide) source012_valid tests48_012_2241 fee48_012_22736 (by decide +kernel)

private theorem range48From22001 : Win 48 22001 22736 :=
  complete (by decide) (by decide) (join_population (join_population range48From22001To2099 (join_population range48From22001To2155 range48From22001To2178)) (join_population range48From22001To2219 (join_population range48From22001To2241 range48From22001To2257)))

private theorem fee48_007_23674 :
    PopulationFees20258.bill (n:=23674) (PopulationFees20258.tabulate (23674-1) 256) source007.plan.table+
      4*23674*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*87093074096 := by decide +kernel
private theorem range48From22737To2118 : Segment 48 22737 23674 0 2118 :=
  paid (pc:=78) (v:=87093074096) (by decide) source007_valid tests48_007_0 fee48_007_23674 (by decide +kernel)

private theorem tests48_009_2118 : ∀ z∈source009.plan.table,z.1.Valid 48 2118 := by decide +kernel
private theorem fee48_009_23674 :
    PopulationFees20258.bill (n:=23674) (PopulationFees20258.tabulate (23674-1) 256) source009.plan.table+
      4*23674*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*218331544965 := by decide +kernel
private theorem range48From22737To2179 : Segment 48 22737 23674 2118 2179 :=
  paid (pc:=78) (v:=218331544965) (by decide) source009_valid tests48_009_2118 fee48_009_23674 (by decide +kernel)

private theorem tests48_013_2179 : ∀ z∈source013.plan.table,z.1.Valid 48 2179 := by decide +kernel
private theorem fee48_013_23674 :
    PopulationFees20258.bill (n:=23674) (PopulationFees20258.tabulate (23674-1) 256) source013.plan.table+
      4*23674*NaturalPopulation20258.weights source013.extras≤source013.plan.scale*207954153387 := by decide +kernel
private theorem range48From22737To2219 : Segment 48 22737 23674 2179 2219 :=
  paid (pc:=77) (v:=207954153387) (by decide) source013_valid tests48_013_2179 fee48_013_23674 (by decide +kernel)

private theorem fee48_011_23674 :
    PopulationFees20258.bill (n:=23674) (PopulationFees20258.tabulate (23674-1) 256) source011.plan.table+
      4*23674*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*202506477259 := by decide +kernel
private theorem range48From22737To2241 : Segment 48 22737 23674 2219 2241 :=
  paid (pc:=77) (v:=202506477259) (by decide) source011_valid tests48_011_2219 fee48_011_23674 (by decide +kernel)

private theorem fee48_012_23674 :
    PopulationFees20258.bill (n:=23674) (PopulationFees20258.tabulate (23674-1) 256) source012.plan.table+
      4*23674*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*197093204578 := by decide +kernel
private theorem range48From22737To2257 : Segment 48 22737 23674 2241 2257 :=
  paid (pc:=77) (v:=197093204578) (by decide) source012_valid tests48_012_2241 fee48_012_23674 (by decide +kernel)

private theorem range48From22737 : Win 48 22737 23674 :=
  complete (by decide) (by decide) (join_population (join_population range48From22737To2118 range48From22737To2179) (join_population range48From22737To2219 (join_population range48From22737To2241 range48From22737To2257)))

private theorem fee48_007_24888 :
    PopulationFees20258.bill (n:=24888) (PopulationFees20258.tabulate (24888-1) 256) source007.plan.table+
      4*24888*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*95823605254 := by decide +kernel
private theorem range48From23675To2140 : Segment 48 23675 24888 0 2140 :=
  paid (pc:=77) (v:=95823605254) (by decide) source007_valid tests48_007_0 fee48_007_24888 (by decide +kernel)

private theorem tests48_009_2140 : ∀ z∈source009.plan.table,z.1.Valid 48 2140 := by decide +kernel
private theorem fee48_009_24888 :
    PopulationFees20258.bill (n:=24888) (PopulationFees20258.tabulate (24888-1) 256) source009.plan.table+
      4*24888*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*239709061760 := by decide +kernel
private theorem range48From23675To2181 : Segment 48 23675 24888 2140 2181 :=
  paid (pc:=77) (v:=239709061760) (by decide) source009_valid tests48_009_2140 fee48_009_24888 (by decide +kernel)

private theorem tests48_013_2181 : ∀ z∈source013.plan.table,z.1.Valid 48 2181 := by decide +kernel
private theorem fee48_013_24888 :
    PopulationFees20258.bill (n:=24888) (PopulationFees20258.tabulate (24888-1) 256) source013.plan.table+
      4*24888*NaturalPopulation20258.weights source013.extras≤source013.plan.scale*228353763108 := by decide +kernel
private theorem range48From23675To2220 : Segment 48 23675 24888 2181 2220 :=
  paid (pc:=77) (v:=228353763108) (by decide) source013_valid tests48_013_2181 fee48_013_24888 (by decide +kernel)

private theorem tests48_011_2220 : ∀ z∈source011.plan.table,z.1.Valid 48 2220 := by decide +kernel
private theorem fee48_011_24888 :
    PopulationFees20258.bill (n:=24888) (PopulationFees20258.tabulate (24888-1) 256) source011.plan.table+
      4*24888*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*222415391575 := by decide +kernel
private theorem range48From23675To2241 : Segment 48 23675 24888 2220 2241 :=
  paid (pc:=77) (v:=222415391575) (by decide) source011_valid tests48_011_2220 fee48_011_24888 (by decide +kernel)

private theorem fee48_012_24888 :
    PopulationFees20258.bill (n:=24888) (PopulationFees20258.tabulate (24888-1) 256) source012.plan.table+
      4*24888*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*216501688322 := by decide +kernel
private theorem range48From23675To2257 : Segment 48 23675 24888 2241 2257 :=
  paid (pc:=77) (v:=216501688322) (by decide) source012_valid tests48_012_2241 fee48_012_24888 (by decide +kernel)

private theorem range48From23675 : Win 48 23675 24888 :=
  complete (by decide) (by decide) (join_population (join_population range48From23675To2140 range48From23675To2181) (join_population range48From23675To2220 (join_population range48From23675To2241 range48From23675To2257)))

private theorem fee48_007_26484 :
    PopulationFees20258.bill (n:=26484) (PopulationFees20258.tabulate (26484-1) 256) source007.plan.table+
      4*26484*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*107905750195 := by decide +kernel
private theorem range48From24889To2165 : Segment 48 24889 26484 0 2165 :=
  paid (pc:=77) (v:=107905750195) (by decide) source007_valid tests48_007_0 fee48_007_26484 (by decide +kernel)

private theorem tests48_009_2165 : ∀ z∈source009.plan.table,z.1.Valid 48 2165 := by decide +kernel
private theorem fee48_009_26484 :
    PopulationFees20258.bill (n:=26484) (PopulationFees20258.tabulate (26484-1) 256) source009.plan.table+
      4*26484*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*269293484331 := by decide +kernel
private theorem range48From24889To2185 : Segment 48 24889 26484 2165 2185 :=
  paid (pc:=77) (v:=269293484331) (by decide) source009_valid tests48_009_2165 fee48_009_26484 (by decide +kernel)

private theorem tests48_013_2185 : ∀ z∈source013.plan.table,z.1.Valid 48 2185 := by decide +kernel
private theorem fee48_013_26484 :
    PopulationFees20258.bill (n:=26484) (PopulationFees20258.tabulate (26484-1) 256) source013.plan.table+
      4*26484*NaturalPopulation20258.weights source013.extras≤source013.plan.scale*256565625107 := by decide +kernel
private theorem range48From24889To2221 : Segment 48 24889 26484 2185 2221 :=
  paid (pc:=76) (v:=256565625107) (by decide) source013_valid tests48_013_2185 fee48_013_26484 (by decide +kernel)

private theorem tests48_011_2221 : ∀ z∈source011.plan.table,z.1.Valid 48 2221 := by decide +kernel
private theorem fee48_011_26484 :
    PopulationFees20258.bill (n:=26484) (PopulationFees20258.tabulate (26484-1) 256) source011.plan.table+
      4*26484*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*249935410558 := by decide +kernel
private theorem range48From24889To2241 : Segment 48 24889 26484 2221 2241 :=
  paid (pc:=76) (v:=249935410558) (by decide) source011_valid tests48_011_2221 fee48_011_26484 (by decide +kernel)

private theorem fee48_012_26484 :
    PopulationFees20258.bill (n:=26484) (PopulationFees20258.tabulate (26484-1) 256) source012.plan.table+
      4*26484*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*243329044966 := by decide +kernel
private theorem range48From24889To2257 : Segment 48 24889 26484 2241 2257 :=
  paid (pc:=76) (v:=243329044966) (by decide) source012_valid tests48_012_2241 fee48_012_26484 (by decide +kernel)

private theorem range48From24889 : Win 48 24889 26484 :=
  complete (by decide) (by decide) (join_population (join_population range48From24889To2165 range48From24889To2185) (join_population range48From24889To2221 (join_population range48From24889To2241 range48From24889To2257)))

private theorem range48From26485 : Win 48 26485 39999 :=
  short (by decide) (by decide)

theorem cut48From22001 : Win 48 22001 39999 :=
  (join_ground (join_ground range48From22001 range48From22737) (join_ground range48From23675 (join_ground range48From24889 range48From26485)))

end JSP233.FiniteCutRanges20258
