module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source014
public import Erdos272.Arithmetic.N20258.Sources.Source015
public import Erdos272.Arithmetic.N20258.Sources.Source017
public import Erdos272.Arithmetic.N20258.Sources.Source018
public import Erdos272.Arithmetic.N20258.Sources.Source019
public import Erdos272.Arithmetic.N20258.Sources.Source021
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
private theorem fee49_014_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source014.plan.table+
      4*22393*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*116285587610 := by decide +kernel
private theorem range49From21794To2141 : Segment 49 21794 22393 0 2141 :=
  paid (pc:=79) (v:=116285587610) (by decide) source014_valid tests49_014_0 fee49_014_22393 (by decide +kernel)

private theorem tests49_015_2141 : ∀ z∈source015.plan.table,z.1.Valid 49 2141 := by decide +kernel
private theorem fee49_015_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source015.plan.table+
      4*22393*NaturalPopulation20258.weights source015.extras≤source015.plan.scale*149214682977 := by decide +kernel
private theorem range49From21794To2199 : Segment 49 21794 22393 2141 2199 :=
  paid (pc:=78) (v:=149214682977) (by decide) source015_valid tests49_015_2141 fee49_015_22393 (by decide +kernel)

private theorem tests49_018_2199 : ∀ z∈source018.plan.table,z.1.Valid 49 2199 := by decide +kernel
private theorem fee49_018_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source018.plan.table+
      4*22393*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*184720723428 := by decide +kernel
private theorem range49From21794To2255 : Segment 49 21794 22393 2199 2255 :=
  paid (pc:=78) (v:=184720723428) (by decide) source018_valid tests49_018_2199 fee49_018_22393 (by decide +kernel)

private theorem tests49_019_2255 : ∀ z∈source019.plan.table,z.1.Valid 49 2255 := by decide +kernel
private theorem fee49_019_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source019.plan.table+
      4*22393*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*180404256781 := by decide +kernel
private theorem range49From21794To2274 : Segment 49 21794 22393 2255 2274 :=
  paid (pc:=78) (v:=180404256781) (by decide) source019_valid tests49_019_2255 fee49_019_22393 (by decide +kernel)

private theorem tests49_023_2274 : ∀ z∈source023.plan.table,z.1.Valid 49 2274 := by decide +kernel
private theorem fee49_023_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source023.plan.table+
      4*22393*NaturalPopulation20258.weights source023.extras≤source023.plan.scale*228152303587 := by decide +kernel
private theorem range49From21794To2285 : Segment 49 21794 22393 2274 2285 :=
  paid (pc:=78) (v:=228152303587) (by decide) source023_valid tests49_023_2274 fee49_023_22393 (by decide +kernel)

private theorem tests49_024_2285 : ∀ z∈source024.plan.table,z.1.Valid 49 2285 := by decide +kernel
private theorem fee49_024_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source024.plan.table+
      4*22393*NaturalPopulation20258.weights source024.extras≤source024.plan.scale*223102218542 := by decide +kernel
private theorem range49From21794To2309 : Segment 49 21794 22393 2285 2309 :=
  paid (pc:=77) (v:=223102218542) (by decide) source024_valid tests49_024_2285 fee49_024_22393 (by decide +kernel)

private theorem tests49_027_2309 : ∀ z∈source027.plan.table,z.1.Valid 49 2309 := by decide +kernel
private theorem fee49_027_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source027.plan.table+
      4*22393*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*222700114073 := by decide +kernel
private theorem range49From21794To2312 : Segment 49 21794 22393 2309 2312 :=
  paid (pc:=77) (v:=222700114073) (by decide) source027_valid tests49_027_2309 fee49_027_22393 (by decide +kernel)

private theorem tests49_025_2312 : ∀ z∈source025.plan.table,z.1.Valid 49 2312 := by decide +kernel
private theorem fee49_025_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source025.plan.table+
      4*22393*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*218740473342 := by decide +kernel
private theorem range49From21794To2332 : Segment 49 21794 22393 2312 2332 :=
  paid (pc:=77) (v:=218740473342) (by decide) source025_valid tests49_025_2312 fee49_025_22393 (by decide +kernel)

private theorem tests49_021_2332 : ∀ z∈source021.plan.table,z.1.Valid 49 2332 := by decide +kernel
private theorem fee49_021_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source021.plan.table+
      4*22393*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*217307817007 := by decide +kernel
private theorem range49From21794To2339 : Segment 49 21794 22393 2332 2339 :=
  paid (pc:=77) (v:=217307817007) (by decide) source021_valid tests49_021_2332 fee49_021_22393 (by decide +kernel)

private theorem tests49_026_2339 : ∀ z∈source026.plan.table,z.1.Valid 49 2339 := by decide +kernel
private theorem fee49_026_22393 :
    PopulationFees20258.bill (n:=22393) (PopulationFees20258.tabulate (22393-1) 256) source026.plan.table+
      4*22393*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*212628728097 := by decide +kernel
private theorem range49From21794To2353 : Segment 49 21794 22393 2339 2353 :=
  paid (pc:=77) (v:=212628728097) (by decide) source026_valid tests49_026_2339 fee49_026_22393 (by decide +kernel)

private theorem range49From21794 : Win 49 21794 22393 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range49From21794To2141 range49From21794To2199) (join_population range49From21794To2255 (join_population range49From21794To2274 range49From21794To2285))) (join_population (join_population range49From21794To2309 range49From21794To2312) (join_population range49From21794To2332 (join_population range49From21794To2339 range49From21794To2353))))

private theorem fee49_014_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source014.plan.table+
      4*23130*NaturalPopulation20258.weights source014.extras≤source014.plan.scale*123589883272 := by decide +kernel
private theorem range49From22394To2159 : Segment 49 22394 23130 0 2159 :=
  paid (pc:=78) (v:=123589883272) (by decide) source014_valid tests49_014_0 fee49_014_23130 (by decide +kernel)

private theorem tests49_017_2159 : ∀ z∈source017.plan.table,z.1.Valid 49 2159 := by decide +kernel
private theorem fee49_017_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source017.plan.table+
      4*23130*NaturalPopulation20258.weights source017.extras≤source017.plan.scale*204049091488 := by decide +kernel
private theorem range49From22394To2230 : Segment 49 22394 23130 2159 2230 :=
  paid (pc:=78) (v:=204049091488) (by decide) source017_valid tests49_017_2159 fee49_017_23130 (by decide +kernel)

private theorem tests49_019_2230 : ∀ z∈source019.plan.table,z.1.Valid 49 2230 := by decide +kernel
private theorem fee49_019_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source019.plan.table+
      4*23130*NaturalPopulation20258.weights source019.extras≤source019.plan.scale*191636269157 := by decide +kernel
private theorem range49From22394To2281 : Segment 49 22394 23130 2230 2281 :=
  paid (pc:=78) (v:=191636269157) (by decide) source019_valid tests49_019_2230 fee49_019_23130 (by decide +kernel)

private theorem tests49_023_2281 : ∀ z∈source023.plan.table,z.1.Valid 49 2281 := by decide +kernel
private theorem fee49_023_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source023.plan.table+
      4*23130*NaturalPopulation20258.weights source023.extras≤source023.plan.scale*242259845332 := by decide +kernel
private theorem range49From22394To2287 : Segment 49 22394 23130 2281 2287 :=
  paid (pc:=77) (v:=242259845332) (by decide) source023_valid tests49_023_2281 fee49_023_23130 (by decide +kernel)

private theorem tests49_024_2287 : ∀ z∈source024.plan.table,z.1.Valid 49 2287 := by decide +kernel
private theorem fee49_024_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source024.plan.table+
      4*23130*NaturalPopulation20258.weights source024.extras≤source024.plan.scale*236911119793 := by decide +kernel
private theorem range49From22394To2310 : Segment 49 22394 23130 2287 2310 :=
  paid (pc:=77) (v:=236911119793) (by decide) source024_valid tests49_024_2287 fee49_024_23130 (by decide +kernel)

private theorem tests49_027_2310 : ∀ z∈source027.plan.table,z.1.Valid 49 2310 := by decide +kernel
private theorem fee49_027_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source027.plan.table+
      4*23130*NaturalPopulation20258.weights source027.extras≤source027.plan.scale*236485544663 := by decide +kernel
private theorem range49From22394To2313 : Segment 49 22394 23130 2310 2313 :=
  paid (pc:=77) (v:=236485544663) (by decide) source027_valid tests49_027_2310 fee49_027_23130 (by decide +kernel)

private theorem tests49_025_2313 : ∀ z∈source025.plan.table,z.1.Valid 49 2313 := by decide +kernel
private theorem fee49_025_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source025.plan.table+
      4*23130*NaturalPopulation20258.weights source025.extras≤source025.plan.scale*232291580853 := by decide +kernel
private theorem range49From22394To2332 : Segment 49 22394 23130 2313 2332 :=
  paid (pc:=77) (v:=232291580853) (by decide) source025_valid tests49_025_2313 fee49_025_23130 (by decide +kernel)

private theorem fee49_021_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source021.plan.table+
      4*23130*NaturalPopulation20258.weights source021.extras≤source021.plan.scale*230777920202 := by decide +kernel
private theorem range49From22394To2339 : Segment 49 22394 23130 2332 2339 :=
  paid (pc:=77) (v:=230777920202) (by decide) source021_valid tests49_021_2332 fee49_021_23130 (by decide +kernel)

private theorem fee49_026_23130 :
    PopulationFees20258.bill (n:=23130) (PopulationFees20258.tabulate (23130-1) 256) source026.plan.table+
      4*23130*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*225831270955 := by decide +kernel
private theorem range49From22394To2353 : Segment 49 22394 23130 2339 2353 :=
  paid (pc:=77) (v:=225831270955) (by decide) source026_valid tests49_026_2339 fee49_026_23130 (by decide +kernel)

private theorem range49From22394 : Win 49 22394 23130 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range49From22394To2159 range49From22394To2230) (join_population range49From22394To2281 range49From22394To2287)) (join_population (join_population range49From22394To2310 range49From22394To2313) (join_population range49From22394To2332 (join_population range49From22394To2339 range49From22394To2353))))

theorem cut49From21794 : Win 49 21794 23130 :=
  (join_ground range49From21794 range49From22394)

end JSP233.FiniteCutRanges20258
