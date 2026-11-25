module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source007
public import Erdos272.Arithmetic.N20258.Sources.Source008
public import Erdos272.Arithmetic.N20258.Sources.Source009
public import Erdos272.Arithmetic.N20258.Sources.Source010
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
private theorem fee48_007_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source007.plan.table+
      4*20567*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*66636707636 := by decide +kernel
private theorem range48From20258To2047 : Segment 48 20258 20567 0 2047 :=
  paid (pc:=80) (v:=66636707636) (by decide) source007_valid tests48_007_0 fee48_007_20567 (by decide +kernel)

private theorem tests48_008_2047 : ∀ z∈source008.plan.table,z.1.Valid 48 2047 := by decide +kernel
private theorem fee48_008_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source008.plan.table+
      4*20567*NaturalPopulation20258.weights source008.extras≤source008.plan.scale*132732965969 := by decide +kernel
private theorem range48From20258To2130 : Segment 48 20258 20567 2047 2130 :=
  paid (pc:=79) (v:=132732965969) (by decide) source008_valid tests48_008_2047 fee48_008_20567 (by decide +kernel)

private theorem tests48_009_2130 : ∀ z∈source009.plan.table,z.1.Valid 48 2130 := by decide +kernel
private theorem fee48_009_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source009.plan.table+
      4*20567*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*168109268247 := by decide +kernel
private theorem range48From20258To2172 : Segment 48 20258 20567 2130 2172 :=
  paid (pc:=79) (v:=168109268247) (by decide) source009_valid tests48_009_2130 fee48_009_20567 (by decide +kernel)

private theorem tests48_010_2172 : ∀ z∈source010.plan.table,z.1.Valid 48 2172 := by decide +kernel
private theorem fee48_010_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source010.plan.table+
      4*20567*NaturalPopulation20258.weights source010.extras≤source010.plan.scale*161261641513 := by decide +kernel
private theorem range48From20258To2210 : Segment 48 20258 20567 2172 2210 :=
  paid (pc:=78) (v:=161261641513) (by decide) source010_valid tests48_010_2172 fee48_010_20567 (by decide +kernel)

private theorem tests48_011_2210 : ∀ z∈source011.plan.table,z.1.Valid 48 2210 := by decide +kernel
private theorem fee48_011_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source011.plan.table+
      4*20567*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*155783796616 := by decide +kernel
private theorem range48From20258To2241 : Segment 48 20258 20567 2210 2241 :=
  paid (pc:=78) (v:=155783796616) (by decide) source011_valid tests48_011_2210 fee48_011_20567 (by decide +kernel)

private theorem tests48_012_2241 : ∀ z∈source012.plan.table,z.1.Valid 48 2241 := by decide +kernel
private theorem fee48_012_20567 :
    PopulationFees20258.bill (n:=20567) (PopulationFees20258.tabulate (20567-1) 256) source012.plan.table+
      4*20567*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*151549526326 := by decide +kernel
private theorem range48From20258To2257 : Segment 48 20258 20567 2241 2257 :=
  paid (pc:=78) (v:=151549526326) (by decide) source012_valid tests48_012_2241 fee48_012_20567 (by decide +kernel)

private theorem range48From20258 : Win 48 20258 20567 :=
  complete (by decide) (by decide) (join_population (join_population range48From20258To2047 (join_population range48From20258To2130 range48From20258To2172)) (join_population range48From20258To2210 (join_population range48From20258To2241 range48From20258To2257)))

private theorem fee48_007_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source007.plan.table+
      4*20946*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*68989991526 := by decide +kernel
private theorem range48From20568To2058 : Segment 48 20568 20946 0 2058 :=
  paid (pc:=79) (v:=68989991526) (by decide) source007_valid tests48_007_0 fee48_007_20946 (by decide +kernel)

private theorem tests48_008_2058 : ∀ z∈source008.plan.table,z.1.Valid 48 2058 := by decide +kernel
private theorem fee48_008_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source008.plan.table+
      4*20946*NaturalPopulation20258.weights source008.extras≤source008.plan.scale*137329304391 := by decide +kernel
private theorem range48From20568To2135 : Segment 48 20568 20946 2058 2135 :=
  paid (pc:=79) (v:=137329304391) (by decide) source008_valid tests48_008_2058 fee48_008_20946 (by decide +kernel)

private theorem tests48_009_2135 : ∀ z∈source009.plan.table,z.1.Valid 48 2135 := by decide +kernel
private theorem fee48_009_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source009.plan.table+
      4*20946*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*173899062863 := by decide +kernel
private theorem range48From20568To2173 : Segment 48 20568 20946 2135 2173 :=
  paid (pc:=78) (v:=173899062863) (by decide) source009_valid tests48_009_2135 fee48_009_20946 (by decide +kernel)

private theorem tests48_010_2173 : ∀ z∈source010.plan.table,z.1.Valid 48 2173 := by decide +kernel
private theorem fee48_010_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source010.plan.table+
      4*20946*NaturalPopulation20258.weights source010.extras≤source010.plan.scale*166829567258 := by decide +kernel
private theorem range48From20568To2210 : Segment 48 20568 20946 2173 2210 :=
  paid (pc:=78) (v:=166829567258) (by decide) source010_valid tests48_010_2173 fee48_010_20946 (by decide +kernel)

private theorem fee48_011_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source011.plan.table+
      4*20946*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*161175509937 := by decide +kernel
private theorem range48From20568To2241 : Segment 48 20568 20946 2210 2241 :=
  paid (pc:=78) (v:=161175509937) (by decide) source011_valid tests48_011_2210 fee48_011_20946 (by decide +kernel)

private theorem fee48_012_20946 :
    PopulationFees20258.bill (n:=20946) (PopulationFees20258.tabulate (20946-1) 256) source012.plan.table+
      4*20946*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*156802585565 := by decide +kernel
private theorem range48From20568To2257 : Segment 48 20568 20946 2241 2257 :=
  paid (pc:=78) (v:=156802585565) (by decide) source012_valid tests48_012_2241 fee48_012_20946 (by decide +kernel)

private theorem range48From20568 : Win 48 20568 20946 :=
  complete (by decide) (by decide) (join_population (join_population range48From20568To2058 (join_population range48From20568To2135 range48From20568To2173)) (join_population range48From20568To2210 (join_population range48From20568To2241 range48From20568To2257)))

private theorem fee48_007_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source007.plan.table+
      4*21416*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*71919319105 := by decide +kernel
private theorem range48From20947To2070 : Segment 48 20947 21416 0 2070 :=
  paid (pc:=79) (v:=71919319105) (by decide) source007_valid tests48_007_0 fee48_007_21416 (by decide +kernel)

private theorem tests48_008_2070 : ∀ z∈source008.plan.table,z.1.Valid 48 2070 := by decide +kernel
private theorem fee48_008_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source008.plan.table+
      4*21416*NaturalPopulation20258.weights source008.extras≤source008.plan.scale*143055755373 := by decide +kernel
private theorem range48From20947To2141 : Segment 48 20947 21416 2070 2141 :=
  paid (pc:=79) (v:=143055755373) (by decide) source008_valid tests48_008_2070 fee48_008_21416 (by decide +kernel)

private theorem tests48_009_2141 : ∀ z∈source009.plan.table,z.1.Valid 48 2141 := by decide +kernel
private theorem fee48_009_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source009.plan.table+
      4*21416*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*181110357427 := by decide +kernel
private theorem range48From20947To2175 : Segment 48 20947 21416 2141 2175 :=
  paid (pc:=78) (v:=181110357427) (by decide) source009_valid tests48_009_2141 fee48_009_21416 (by decide +kernel)

private theorem tests48_010_2175 : ∀ z∈source010.plan.table,z.1.Valid 48 2175 := by decide +kernel
private theorem fee48_010_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source010.plan.table+
      4*21416*NaturalPopulation20258.weights source010.extras≤source010.plan.scale*173757049908 := by decide +kernel
private theorem range48From20947To2211 : Segment 48 20947 21416 2175 2211 :=
  paid (pc:=78) (v:=173757049908) (by decide) source010_valid tests48_010_2175 fee48_010_21416 (by decide +kernel)

private theorem tests48_011_2211 : ∀ z∈source011.plan.table,z.1.Valid 48 2211 := by decide +kernel
private theorem fee48_011_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source011.plan.table+
      4*21416*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*167872967742 := by decide +kernel
private theorem range48From20947To2241 : Segment 48 20947 21416 2211 2241 :=
  paid (pc:=78) (v:=167872967742) (by decide) source011_valid tests48_011_2211 fee48_011_21416 (by decide +kernel)

private theorem fee48_012_21416 :
    PopulationFees20258.bill (n:=21416) (PopulationFees20258.tabulate (21416-1) 256) source012.plan.table+
      4*21416*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*163332588201 := by decide +kernel
private theorem range48From20947To2257 : Segment 48 20947 21416 2241 2257 :=
  paid (pc:=78) (v:=163332588201) (by decide) source012_valid tests48_012_2241 fee48_012_21416 (by decide +kernel)

private theorem range48From20947 : Win 48 20947 21416 :=
  complete (by decide) (by decide) (join_population (join_population range48From20947To2070 (join_population range48From20947To2141 range48From20947To2175)) (join_population range48From20947To2211 (join_population range48From20947To2241 range48From20947To2257)))

private theorem fee48_007_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source007.plan.table+
      4*22000*NaturalPopulation20258.weights source007.extras≤source007.plan.scale*75680356522 := by decide +kernel
private theorem range48From21417To2084 : Segment 48 21417 22000 0 2084 :=
  paid (pc:=79) (v:=75680356522) (by decide) source007_valid tests48_007_0 fee48_007_22000 (by decide +kernel)

private theorem tests48_008_2084 : ∀ z∈source008.plan.table,z.1.Valid 48 2084 := by decide +kernel
private theorem fee48_008_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source008.plan.table+
      4*22000*NaturalPopulation20258.weights source008.extras≤source008.plan.scale*150413410820 := by decide +kernel
private theorem range48From21417To2148 : Segment 48 21417 22000 2084 2148 :=
  paid (pc:=78) (v:=150413410820) (by decide) source008_valid tests48_008_2084 fee48_008_22000 (by decide +kernel)

private theorem tests48_009_2148 : ∀ z∈source009.plan.table,z.1.Valid 48 2148 := by decide +kernel
private theorem fee48_009_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source009.plan.table+
      4*22000*NaturalPopulation20258.weights source009.extras≤source009.plan.scale*190374594784 := by decide +kernel
private theorem range48From21417To2177 : Segment 48 21417 22000 2148 2177 :=
  paid (pc:=78) (v:=190374594784) (by decide) source009_valid tests48_009_2148 fee48_009_22000 (by decide +kernel)

private theorem tests48_013_2177 : ∀ z∈source013.plan.table,z.1.Valid 48 2177 := by decide +kernel
private theorem fee48_013_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source013.plan.table+
      4*22000*NaturalPopulation20258.weights source013.extras≤source013.plan.scale*181265038791 := by decide +kernel
private theorem range48From21417To2219 : Segment 48 21417 22000 2177 2219 :=
  paid (pc:=78) (v:=181265038791) (by decide) source013_valid tests48_013_2177 fee48_013_22000 (by decide +kernel)

private theorem tests48_011_2219 : ∀ z∈source011.plan.table,z.1.Valid 48 2219 := by decide +kernel
private theorem fee48_011_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source011.plan.table+
      4*22000*NaturalPopulation20258.weights source011.extras≤source011.plan.scale*176478156947 := by decide +kernel
private theorem range48From21417To2241 : Segment 48 21417 22000 2219 2241 :=
  paid (pc:=78) (v:=176478156947) (by decide) source011_valid tests48_011_2219 fee48_011_22000 (by decide +kernel)

private theorem fee48_012_22000 :
    PopulationFees20258.bill (n:=22000) (PopulationFees20258.tabulate (22000-1) 256) source012.plan.table+
      4*22000*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*171716933690 := by decide +kernel
private theorem range48From21417To2257 : Segment 48 21417 22000 2241 2257 :=
  paid (pc:=77) (v:=171716933690) (by decide) source012_valid tests48_012_2241 fee48_012_22000 (by decide +kernel)

private theorem range48From21417 : Win 48 21417 22000 :=
  complete (by decide) (by decide) (join_population (join_population range48From21417To2084 (join_population range48From21417To2148 range48From21417To2177)) (join_population range48From21417To2219 (join_population range48From21417To2241 range48From21417To2257)))

theorem cut48From20258 : Win 48 20258 22000 :=
  (join_ground (join_ground range48From20258 range48From20568) (join_ground range48From20947 range48From21417))

end JSP233.FiniteCutRanges20258
