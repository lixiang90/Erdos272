module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source012
public import Erdos272.Arithmetic.N20258.Sources.Source014
public import Erdos272.Arithmetic.N20258.Sources.Source016
public import Erdos272.Arithmetic.N20258.Sources.Source018
public import Erdos272.Arithmetic.N20258.Sources.Source019
public import Erdos272.Arithmetic.N20258.Sources.Source021
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
private theorem fee49_014_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source014.plan.table+
      4*24047*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*132985785172 := by decide +kernel
private theorem range49From23131To2180 : Segment 49 23131 24047 0 2180 :=
  paid (pc:=78) (v:=132985785172) (by decide) source014_valid tests49_014_0 fee49_014_24047 (by decide +kernel)

private theorem tests49_016_2180 : ∀ z∈source016.plan.table,z.1.Valid 49 2180 := by decide +kernel
private theorem fee49_016_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source016.plan.table+
      4*24047*NaturalPopulation20258.weights source016.extras≤source016.plan.scale*214504422029 := by decide +kernel
private theorem range49From23131To2258 : Segment 49 23131 24047 2180 2258 :=
  paid (pc:=77) (v:=214504422029) (by decide) source016_valid tests49_016_2180 fee49_016_24047 (by decide +kernel)

private theorem tests49_019_2258 : ∀ z∈source019.plan.table,z.1.Valid 49 2258 := by decide +kernel
private theorem fee49_019_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source019.plan.table+
      4*24047*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*206076090236 := by decide +kernel
private theorem range49From23131To2290 : Segment 49 23131 24047 2258 2290 :=
  paid (pc:=77) (v:=206076090236) (by decide) source019_valid tests49_019_2258 fee49_019_24047 (by decide +kernel)

private theorem tests49_027_2290 : ∀ z∈source027.plan.table,z.1.Valid 49 2290 := by decide +kernel
private theorem fee49_027_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source027.plan.table+
      4*24047*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*254198696658 := by decide +kernel
private theorem range49From23131To2313 : Segment 49 23131 24047 2290 2313 :=
  paid (pc:=77) (v:=254198696658) (by decide) source027_valid tests49_027_2290 fee49_027_24047 (by decide +kernel)

private theorem tests49_025_2313 : ∀ z∈source025.plan.table,z.1.Valid 49 2313 := by decide +kernel
private theorem fee49_025_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source025.plan.table+
      4*24047*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*249710037755 := by decide +kernel
private theorem range49From23131To2332 : Segment 49 23131 24047 2313 2332 :=
  paid (pc:=77) (v:=249710037755) (by decide) source025_valid tests49_025_2313 fee49_025_24047 (by decide +kernel)

private theorem tests49_021_2332 : ∀ z∈source021.plan.table,z.1.Valid 49 2332 := by decide +kernel
private theorem fee49_021_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source021.plan.table+
      4*24047*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*248092169128 := by decide +kernel
private theorem range49From23131To2339 : Segment 49 23131 24047 2332 2339 :=
  paid (pc:=77) (v:=248092169128) (by decide) source021_valid tests49_021_2332 fee49_021_24047 (by decide +kernel)

private theorem tests49_026_2339 : ∀ z∈source026.plan.table,z.1.Valid 49 2339 := by decide +kernel
private theorem fee49_026_24047 :
    PopulationFees20258.bill (n:=24047) (PopulationFees20258.tabulate (24047-1) 256) source026.plan.table+
      4*24047*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*242784548929 := by decide +kernel
private theorem range49From23131To2353 : Segment 49 23131 24047 2339 2353 :=
  paid (pc:=77) (v:=242784548929) (by decide) source026_valid tests49_026_2339 fee49_026_24047 (by decide +kernel)

private theorem range49From23131 : Win 49 23131 24047 :=
  complete (by decide) (by decide) (join_population (join_population range49From23131To2180 (join_population range49From23131To2258 range49From23131To2290)) (join_population (join_population range49From23131To2313 range49From23131To2332) (join_population range49From23131To2339 range49From23131To2353)))

private theorem fee49_014_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source014.plan.table+
      4*25200*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*145255241140 := by decide +kernel
private theorem range49From24048To2206 : Segment 49 24048 25200 0 2206 :=
  paid (pc:=78) (v:=145255241140) (by decide) source014_valid tests49_014_0 fee49_014_25200 (by decide +kernel)

private theorem tests49_018_2206 : ∀ z∈source018.plan.table,z.1.Valid 49 2206 := by decide +kernel
private theorem fee49_018_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source018.plan.table+
      4*25200*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*230287325827 := by decide +kernel
private theorem range49From24048To2282 : Segment 49 24048 25200 2206 2282 :=
  paid (pc:=77) (v:=230287325827) (by decide) source018_valid tests49_018_2206 fee49_018_25200 (by decide +kernel)

private theorem tests49_019_2282 : ∀ z∈source019.plan.table,z.1.Valid 49 2282 := by decide +kernel
private theorem fee49_019_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source019.plan.table+
      4*25200*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*224956483669 := by decide +kernel
private theorem range49From24048To2301 : Segment 49 24048 25200 2282 2301 :=
  paid (pc:=77) (v:=224956483669) (by decide) source019_valid tests49_019_2282 fee49_019_25200 (by decide +kernel)

private theorem tests49_027_2301 : ∀ z∈source027.plan.table,z.1.Valid 49 2301 := by decide +kernel
private theorem fee49_027_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source027.plan.table+
      4*25200*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*277362975928 := by decide +kernel
private theorem range49From24048To2316 : Segment 49 24048 25200 2301 2316 :=
  paid (pc:=77) (v:=277362975928) (by decide) source027_valid tests49_027_2301 fee49_027_25200 (by decide +kernel)

private theorem tests49_025_2316 : ∀ z∈source025.plan.table,z.1.Valid 49 2316 := by decide +kernel
private theorem fee49_025_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source025.plan.table+
      4*25200*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*272496756878 := by decide +kernel
private theorem range49From24048To2334 : Segment 49 24048 25200 2316 2334 :=
  paid (pc:=77) (v:=272496756878) (by decide) source025_valid tests49_025_2316 fee49_025_25200 (by decide +kernel)

private theorem tests49_021_2334 : ∀ z∈source021.plan.table,z.1.Valid 49 2334 := by decide +kernel
private theorem fee49_021_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source021.plan.table+
      4*25200*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*270738409442 := by decide +kernel
private theorem range49From24048To2341 : Segment 49 24048 25200 2334 2341 :=
  paid (pc:=77) (v:=270738409442) (by decide) source021_valid tests49_021_2334 fee49_021_25200 (by decide +kernel)

private theorem tests49_026_2341 : ∀ z∈source026.plan.table,z.1.Valid 49 2341 := by decide +kernel
private theorem fee49_026_25200 :
    PopulationFees20258.bill (n:=25200) (PopulationFees20258.tabulate (25200-1) 256) source026.plan.table+
      4*25200*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*264976920863 := by decide +kernel
private theorem range49From24048To2353 : Segment 49 24048 25200 2341 2353 :=
  paid (pc:=77) (v:=264976920863) (by decide) source026_valid tests49_026_2341 fee49_026_25200 (by decide +kernel)

private theorem range49From24048 : Win 49 24048 25200 :=
  complete (by decide) (by decide) (join_population (join_population range49From24048To2206 (join_population range49From24048To2282 range49From24048To2301)) (join_population (join_population range49From24048To2316 range49From24048To2334) (join_population range49From24048To2341 range49From24048To2353)))

private theorem fee49_014_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source014.plan.table+
      4*26685*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*161873481447 := by decide +kernel
private theorem range49From25201To2231 : Segment 49 25201 26685 0 2231 :=
  paid (pc:=77) (v:=161873481447) (by decide) source014_valid tests49_014_0 fee49_014_26685 (by decide +kernel)

private theorem tests49_019_2231 : ∀ z∈source019.plan.table,z.1.Valid 49 2231 := by decide +kernel
private theorem fee49_019_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source019.plan.table+
      4*26685*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*250503665767 := by decide +kernel
private theorem range49From25201To2308 : Segment 49 25201 26685 2231 2308 :=
  paid (pc:=76) (v:=250503665767) (by decide) source019_valid tests49_019_2231 fee49_019_26685 (by decide +kernel)

private theorem tests49_012_2308 : ∀ z∈source012.plan.table,z.1.Valid 49 2308 := by decide +kernel
private theorem fee49_012_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source012.plan.table+
      4*26685*NaturalPopulation20258.weights source012.extras≤source012.plan.scale*246929932703 := by decide +kernel
private theorem range49From25201To2320 : Segment 49 25201 26685 2308 2320 :=
  paid (pc:=76) (v:=246929932703) (by decide) source012_valid tests49_012_2308 fee49_012_26685 (by decide +kernel)

private theorem tests49_025_2320 : ∀ z∈source025.plan.table,z.1.Valid 49 2320 := by decide +kernel
private theorem fee49_025_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source025.plan.table+
      4*26685*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*303319790001 := by decide +kernel
private theorem range49From25201To2333 : Segment 49 25201 26685 2320 2333 :=
  paid (pc:=76) (v:=303319790001) (by decide) source025_valid tests49_025_2320 fee49_025_26685 (by decide +kernel)

private theorem tests49_021_2333 : ∀ z∈source021.plan.table,z.1.Valid 49 2333 := by decide +kernel
private theorem fee49_021_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source021.plan.table+
      4*26685*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*301381585140 := by decide +kernel
private theorem range49From25201To2339 : Segment 49 25201 26685 2333 2339 :=
  paid (pc:=76) (v:=301381585140) (by decide) source021_valid tests49_021_2333 fee49_021_26685 (by decide +kernel)

private theorem fee49_026_26685 :
    PopulationFees20258.bill (n:=26685) (PopulationFees20258.tabulate (26685-1) 256) source026.plan.table+
      4*26685*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*295008844248 := by decide +kernel
private theorem range49From25201To2353 : Segment 49 25201 26685 2339 2353 :=
  paid (pc:=76) (v:=295008844248) (by decide) source026_valid tests49_026_2339 fee49_026_26685 (by decide +kernel)

private theorem range49From25201 : Win 49 25201 26685 :=
  complete (by decide) (by decide) (join_population (join_population range49From25201To2231 (join_population range49From25201To2308 range49From25201To2320)) (join_population range49From25201To2333 (join_population range49From25201To2339 range49From25201To2353)))

private theorem fee49_014_28630 :
    PopulationFees20258.bill (n:=28630) (PopulationFees20258.tabulate (28630-1) 256) source014.plan.table+
      4*28630*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*185086874407 := by decide +kernel
private theorem range49From26686To2260 : Segment 49 26686 28630 0 2260 :=
  paid (pc:=76) (v:=185086874407) (by decide) source014_valid tests49_014_0 fee49_014_28630 (by decide +kernel)

private theorem tests49_019_2260 : ∀ z∈source019.plan.table,z.1.Valid 49 2260 := by decide +kernel
private theorem fee49_019_28630 :
    PopulationFees20258.bill (n:=28630) (PopulationFees20258.tabulate (28630-1) 256) source019.plan.table+
      4*28630*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*286156314994 := by decide +kernel
private theorem range49From26686To2321 : Segment 49 26686 28630 2260 2321 :=
  paid (pc:=76) (v:=286156314994) (by decide) source019_valid tests49_019_2260 fee49_019_28630 (by decide +kernel)

private theorem tests49_021_2321 : ∀ z∈source021.plan.table,z.1.Valid 49 2321 := by decide +kernel
private theorem fee49_021_28630 :
    PopulationFees20258.bill (n:=28630) (PopulationFees20258.tabulate (28630-1) 256) source021.plan.table+
      4*28630*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*344070669507 := by decide +kernel
private theorem range49From26686To2339 : Segment 49 26686 28630 2321 2339 :=
  paid (pc:=76) (v:=344070669507) (by decide) source021_valid tests49_021_2321 fee49_021_28630 (by decide +kernel)

private theorem fee49_026_28630 :
    PopulationFees20258.bill (n:=28630) (PopulationFees20258.tabulate (28630-1) 256) source026.plan.table+
      4*28630*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*336853953622 := by decide +kernel
private theorem range49From26686To2353 : Segment 49 26686 28630 2339 2353 :=
  paid (pc:=76) (v:=336853953622) (by decide) source026_valid tests49_026_2339 fee49_026_28630 (by decide +kernel)

private theorem range49From26686 : Win 49 26686 28630 :=
  complete (by decide) (by decide) (join_population (join_population range49From26686To2260 range49From26686To2321) (join_population range49From26686To2339 range49From26686To2353))

theorem cut49From23131 : Win 49 23131 28630 :=
  (join_ground (join_ground range49From23131 range49From24048) (join_ground range49From25201 range49From26686))

end JSP233.FiniteCutRanges20258
