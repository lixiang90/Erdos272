module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source014
public import Erdos272.Arithmetic.N20258.Sources.Source016
public import Erdos272.Arithmetic.N20258.Sources.Source018
public import Erdos272.Arithmetic.N20258.Sources.Source019
public import Erdos272.Arithmetic.N20258.Sources.Source020
public import Erdos272.Arithmetic.N20258.Sources.Source021
public import Erdos272.Arithmetic.N20258.Sources.Source022
public import Erdos272.Arithmetic.N20258.Sources.Source023
public import Erdos272.Arithmetic.N20258.Sources.Source024
public import Erdos272.Arithmetic.N20258.Sources.Source025
public import Erdos272.Arithmetic.N20258.Sources.Source026
public import Erdos272.Arithmetic.N20258.Sources.Source027

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests49_014_0 : ∀ z∈source014.plan.table,z.1.Valid 49 0 := by decide +kernel
private theorem fee49_014_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source014.plan.table+
      4*21298*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*105912907900 := by decide +kernel
private theorem range49From20889To2112 : Segment 49 20889 21298 0 2112 :=
  paid (pc:=79) (v:=105912907900) (by decide) source014_valid tests49_014_0 fee49_014_21298 (by decide +kernel)

private theorem tests49_020_2112 : ∀ z∈source020.plan.table,z.1.Valid 49 2112 := by decide +kernel
private theorem fee49_020_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source020.plan.table+
      4*21298*NaturalPopulation20258.weights source020.extras≤source020.plan.scale*180085943688 := by decide +kernel
private theorem range49From20889To2183 : Segment 49 20889 21298 2112 2183 :=
  paid (pc:=79) (v:=180085943688) (by decide) source020_valid tests49_020_2112 fee49_020_21298 (by decide +kernel)

private theorem tests49_016_2183 : ∀ z∈source016.plan.table,z.1.Valid 49 2183 := by decide +kernel
private theorem fee49_016_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source016.plan.table+
      4*21298*NaturalPopulation20258.weights source016.extras≤source016.plan.scale*171210963233 := by decide +kernel
private theorem range49From20889To2229 : Segment 49 20889 21298 2183 2229 :=
  paid (pc:=78) (v:=171210963233) (by decide) source016_valid tests49_016_2183 fee49_016_21298 (by decide +kernel)

private theorem tests49_019_2229 : ∀ z∈source019.plan.table,z.1.Valid 49 2229 := by decide +kernel
private theorem fee49_019_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source019.plan.table+
      4*21298*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*164414502843 := by decide +kernel
private theorem range49From20889To2263 : Segment 49 20889 21298 2229 2263 :=
  paid (pc:=78) (v:=164414502843) (by decide) source019_valid tests49_019_2229 fee49_019_21298 (by decide +kernel)

private theorem tests49_022_2263 : ∀ z∈source022.plan.table,z.1.Valid 49 2263 := by decide +kernel
private theorem fee49_022_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source022.plan.table+
      4*21298*NaturalPopulation20258.weights source022.extras≤source022.plan.scale*211017710506 := by decide +kernel
private theorem range49From20889To2267 : Segment 49 20889 21298 2263 2267 :=
  paid (pc:=78) (v:=211017710506) (by decide) source022_valid tests49_022_2263 fee49_022_21298 (by decide +kernel)

private theorem tests49_023_2267 : ∀ z∈source023.plan.table,z.1.Valid 49 2267 := by decide +kernel
private theorem fee49_023_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source023.plan.table+
      4*21298*NaturalPopulation20258.weights source023.extras≤source023.plan.scale*208046240807 := by decide +kernel
private theorem range49From20889To2284 : Segment 49 20889 21298 2267 2284 :=
  paid (pc:=78) (v:=208046240807) (by decide) source023_valid tests49_023_2267 fee49_023_21298 (by decide +kernel)

private theorem tests49_024_2284 : ∀ z∈source024.plan.table,z.1.Valid 49 2284 := by decide +kernel
private theorem fee49_024_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source024.plan.table+
      4*21298*NaturalPopulation20258.weights source024.extras≤source024.plan.scale*203421410427 := by decide +kernel
private theorem range49From20889To2309 : Segment 49 20889 21298 2284 2309 :=
  paid (pc:=77) (v:=203421410427) (by decide) source024_valid tests49_024_2284 fee49_024_21298 (by decide +kernel)

private theorem tests49_027_2309 : ∀ z∈source027.plan.table,z.1.Valid 49 2309 := by decide +kernel
private theorem fee49_027_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source027.plan.table+
      4*21298*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*203053084943 := by decide +kernel
private theorem range49From20889To2312 : Segment 49 20889 21298 2309 2312 :=
  paid (pc:=77) (v:=203053084943) (by decide) source027_valid tests49_027_2309 fee49_027_21298 (by decide +kernel)

private theorem tests49_025_2312 : ∀ z∈source025.plan.table,z.1.Valid 49 2312 := by decide +kernel
private theorem fee49_025_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source025.plan.table+
      4*21298*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*199436633358 := by decide +kernel
private theorem range49From20889To2332 : Segment 49 20889 21298 2312 2332 :=
  paid (pc:=77) (v:=199436633358) (by decide) source025_valid tests49_025_2312 fee49_025_21298 (by decide +kernel)

private theorem tests49_021_2332 : ∀ z∈source021.plan.table,z.1.Valid 49 2332 := by decide +kernel
private theorem fee49_021_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source021.plan.table+
      4*21298*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*198121111032 := by decide +kernel
private theorem range49From20889To2340 : Segment 49 20889 21298 2332 2340 :=
  paid (pc:=77) (v:=198121111032) (by decide) source021_valid tests49_021_2332 fee49_021_21298 (by decide +kernel)

private theorem tests49_026_2340 : ∀ z∈source026.plan.table,z.1.Valid 49 2340 := by decide +kernel
private theorem fee49_026_21298 :
    PopulationFees20258.bill (n:=21298) (PopulationFees20258.tabulate (21298-1) 256) source026.plan.table+
      4*21298*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*193820176258 := by decide +kernel
private theorem range49From20889To2353 : Segment 49 20889 21298 2340 2353 :=
  paid (pc:=77) (v:=193820176258) (by decide) source026_valid tests49_026_2340 fee49_026_21298 (by decide +kernel)

private theorem range49From20889 : Win 49 20889 21298 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range49From20889To2112 range49From20889To2183) (join_population range49From20889To2229 (join_population range49From20889To2263 range49From20889To2267))) (join_population (join_population range49From20889To2284 (join_population range49From20889To2309 range49From20889To2312)) (join_population range49From20889To2332 (join_population range49From20889To2340 range49From20889To2353))))

private theorem fee49_014_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source014.plan.table+
      4*21793*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*110534387730 := by decide +kernel
private theorem range49From21299To2124 : Segment 49 21299 21793 0 2124 :=
  paid (pc:=79) (v:=110534387730) (by decide) source014_valid tests49_014_0 fee49_014_21793 (by decide +kernel)

private theorem tests49_020_2124 : ∀ z∈source020.plan.table,z.1.Valid 49 2124 := by decide +kernel
private theorem fee49_020_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source020.plan.table+
      4*21793*NaturalPopulation20258.weights source020.extras≤source020.plan.scale*187849973750 := by decide +kernel
private theorem range49From21299To2190 : Segment 49 21299 21793 2124 2190 :=
  paid (pc:=78) (v:=187849973750) (by decide) source020_valid tests49_020_2124 fee49_020_21793 (by decide +kernel)

private theorem tests49_018_2190 : ∀ z∈source018.plan.table,z.1.Valid 49 2190 := by decide +kernel
private theorem fee49_018_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source018.plan.table+
      4*21793*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*175651944526 := by decide +kernel
private theorem range49From21299To2248 : Segment 49 21299 21793 2190 2248 :=
  paid (pc:=78) (v:=175651944526) (by decide) source018_valid tests49_018_2190 fee49_018_21793 (by decide +kernel)

private theorem tests49_019_2248 : ∀ z∈source019.plan.table,z.1.Valid 49 2248 := by decide +kernel
private theorem fee49_019_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source019.plan.table+
      4*21793*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*171534007927 := by decide +kernel
private theorem range49From21299To2268 : Segment 49 21299 21793 2248 2268 :=
  paid (pc:=78) (v:=171534007927) (by decide) source019_valid tests49_019_2248 fee49_019_21793 (by decide +kernel)

private theorem tests49_023_2268 : ∀ z∈source023.plan.table,z.1.Valid 49 2268 := by decide +kernel
private theorem fee49_023_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source023.plan.table+
      4*21793*NaturalPopulation20258.weights source023.extras≤source023.plan.scale*216992372921 := by decide +kernel
private theorem range49From21299To2284 : Segment 49 21299 21793 2268 2284 :=
  paid (pc:=78) (v:=216992372921) (by decide) source023_valid tests49_023_2268 fee49_023_21793 (by decide +kernel)

private theorem fee49_024_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source024.plan.table+
      4*21793*NaturalPopulation20258.weights source024.extras≤source024.plan.scale*212179531040 := by decide +kernel
private theorem range49From21299To2308 : Segment 49 21299 21793 2284 2308 :=
  paid (pc:=77) (v:=212179531040) (by decide) source024_valid tests49_024_2284 fee49_024_21793 (by decide +kernel)

private theorem tests49_027_2308 : ∀ z∈source027.plan.table,z.1.Valid 49 2308 := by decide +kernel
private theorem fee49_027_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source027.plan.table+
      4*21793*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*211797445342 := by decide +kernel
private theorem range49From21299To2312 : Segment 49 21299 21793 2308 2312 :=
  paid (pc:=77) (v:=211797445342) (by decide) source027_valid tests49_027_2308 fee49_027_21793 (by decide +kernel)

private theorem fee49_025_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source025.plan.table+
      4*21793*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*208015279594 := by decide +kernel
private theorem range49From21299To2331 : Segment 49 21299 21793 2312 2331 :=
  paid (pc:=77) (v:=208015279594) (by decide) source025_valid tests49_025_2312 fee49_025_21793 (by decide +kernel)

private theorem tests49_021_2331 : ∀ z∈source021.plan.table,z.1.Valid 49 2331 := by decide +kernel
private theorem fee49_021_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source021.plan.table+
      4*21793*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*206652015303 := by decide +kernel
private theorem range49From21299To2339 : Segment 49 21299 21793 2331 2339 :=
  paid (pc:=77) (v:=206652015303) (by decide) source021_valid tests49_021_2331 fee49_021_21793 (by decide +kernel)

private theorem tests49_026_2339 : ∀ z∈source026.plan.table,z.1.Valid 49 2339 := by decide +kernel
private theorem fee49_026_21793 :
    PopulationFees20258.bill (n:=21793) (PopulationFees20258.tabulate (21793-1) 256) source026.plan.table+
      4*21793*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*202198539056 := by decide +kernel
private theorem range49From21299To2353 : Segment 49 21299 21793 2339 2353 :=
  paid (pc:=77) (v:=202198539056) (by decide) source026_valid tests49_026_2339 fee49_026_21793 (by decide +kernel)

private theorem range49From21299 : Win 49 21299 21793 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range49From21299To2124 range49From21299To2190) (join_population range49From21299To2248 (join_population range49From21299To2268 range49From21299To2284))) (join_population (join_population range49From21299To2308 range49From21299To2312) (join_population range49From21299To2331 (join_population range49From21299To2339 range49From21299To2353))))

theorem cut49From20889 : Win 49 20889 21793 :=
  (join_ground range49From20889 range49From21299)

end JSP233.FiniteCutRanges20258
