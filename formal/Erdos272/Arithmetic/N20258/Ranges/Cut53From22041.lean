module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source057
public import Erdos272.Arithmetic.N20258.Sources.Source059
public import Erdos272.Arithmetic.N20258.Sources.Source060
public import Erdos272.Arithmetic.N20258.Sources.Source063
public import Erdos272.Arithmetic.N20258.Sources.Source068
public import Erdos272.Arithmetic.N20258.Sources.Source069
public import Erdos272.Arithmetic.N20258.Sources.Source072
public import Erdos272.Arithmetic.N20258.Sources.Source073

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests53_057_0 : ∀ z∈source057.plan.table,z.1.Valid 53 0 := by decide +kernel
private theorem fee53_057_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source057.plan.table+
      4*22484*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*175016691586 := by decide +kernel
private theorem range53From22041To2362 : Segment 53 22041 22484 0 2362 :=
  paid (pc:=78) (v:=175016691586) (by decide) source057_valid tests53_057_0 fee53_057_22484 (by decide +kernel)

private theorem tests53_059_2362 : ∀ z∈source059.plan.table,z.1.Valid 53 2362 := by decide +kernel
private theorem fee53_059_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source059.plan.table+
      4*22484*NaturalPopulation20258.weights source059.extras≤source059.plan.scale*210097453647 := by decide +kernel
private theorem range53From22041To2452 : Segment 53 22041 22484 2362 2452 :=
  paid (pc:=77) (v:=210097453647) (by decide) source059_valid tests53_059_2362 fee53_059_22484 (by decide +kernel)

private theorem tests53_063_2452 : ∀ z∈source063.plan.table,z.1.Valid 53 2452 := by decide +kernel
private theorem fee53_063_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source063.plan.table+
      4*22484*NaturalPopulation20258.weights source063.extras≤source063.plan.scale*253227509397 := by decide +kernel
private theorem range53From22041To2512 : Segment 53 22041 22484 2452 2512 :=
  paid (pc:=77) (v:=253227509397) (by decide) source063_valid tests53_063_2452 fee53_063_22484 (by decide +kernel)

private theorem tests53_068_2512 : ∀ z∈source068.plan.table,z.1.Valid 53 2512 := by decide +kernel
private theorem fee53_068_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source068.plan.table+
      4*22484*NaturalPopulation20258.weights source068.extras≤source068.plan.scale*240857248113 := by decide +kernel
private theorem range53From22041To2581 : Segment 53 22041 22484 2512 2581 :=
  paid (pc:=76) (v:=240857248113) (by decide) source068_valid tests53_068_2512 fee53_068_22484 (by decide +kernel)

private theorem tests53_072_2581 : ∀ z∈source072.plan.table,z.1.Valid 53 2581 := by decide +kernel
private theorem fee53_072_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source072.plan.table+
      4*22484*NaturalPopulation20258.weights source072.extras≤source072.plan.scale*288150569751 := by decide +kernel
private theorem range53From22041To2642 : Segment 53 22041 22484 2581 2642 :=
  paid (pc:=76) (v:=288150569751) (by decide) source072_valid tests53_072_2581 fee53_072_22484 (by decide +kernel)

private theorem tests53_073_2642 : ∀ z∈source073.plan.table,z.1.Valid 53 2642 := by decide +kernel
private theorem fee53_073_22484 :
    PopulationFees20258.bill (n:=22484) (PopulationFees20258.tabulate (22484-1) 256) source073.plan.table+
      4*22484*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*331833478727 := by decide +kernel
private theorem range53From22041To2753 : Segment 53 22041 22484 2642 2753 :=
  paid (pc:=75) (v:=331833478727) (by decide) source073_valid tests53_073_2642 fee53_073_22484 (by decide +kernel)

private theorem tests53_073_2753 : ∀ z∈source073.plan.table,z.1.Valid 53 2753 := by decide +kernel
private theorem range53From22041To2757 : Segment 53 22041 22484 2753 2757 :=
  paid (pc:=75) (v:=331833478727) (by decide) source073_valid tests53_073_2753 fee53_073_22484 (by decide +kernel)

private theorem range53From22041 : Win 53 22041 22484 :=
  complete (by decide) (by decide) (join_population (join_population range53From22041To2362 (join_population range53From22041To2452 range53From22041To2512)) (join_population (join_population range53From22041To2581 range53From22041To2642) (join_population range53From22041To2753 range53From22041To2757)))

private theorem fee53_057_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source057.plan.table+
      4*22976*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*182148783972 := by decide +kernel
private theorem range53From22485To2384 : Segment 53 22485 22976 0 2384 :=
  paid (pc:=78) (v:=182148783972) (by decide) source057_valid tests53_057_0 fee53_057_22976 (by decide +kernel)

private theorem tests53_060_2384 : ∀ z∈source060.plan.table,z.1.Valid 53 2384 := by decide +kernel
private theorem fee53_060_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source060.plan.table+
      4*22976*NaturalPopulation20258.weights source060.extras≤source060.plan.scale*209687059177 := by decide +kernel
private theorem range53From22485To2509 : Segment 53 22485 22976 2384 2509 :=
  paid (pc:=77) (v:=209687059177) (by decide) source060_valid tests53_060_2384 fee53_060_22976 (by decide +kernel)

private theorem tests53_068_2509 : ∀ z∈source068.plan.table,z.1.Valid 53 2509 := by decide +kernel
private theorem fee53_068_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source068.plan.table+
      4*22976*NaturalPopulation20258.weights source068.extras≤source068.plan.scale*250691558800 := by decide +kernel
private theorem range53From22485To2591 : Segment 53 22485 22976 2509 2591 :=
  paid (pc:=76) (v:=250691558800) (by decide) source068_valid tests53_068_2509 fee53_068_22976 (by decide +kernel)

private theorem tests53_072_2591 : ∀ z∈source072.plan.table,z.1.Valid 53 2591 := by decide +kernel
private theorem fee53_072_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source072.plan.table+
      4*22976*NaturalPopulation20258.weights source072.extras≤source072.plan.scale*299854036691 := by decide +kernel
private theorem range53From22485To2646 : Segment 53 22485 22976 2591 2646 :=
  paid (pc:=76) (v:=299854036691) (by decide) source072_valid tests53_072_2591 fee53_072_22976 (by decide +kernel)

private theorem tests53_073_2646 : ∀ z∈source073.plan.table,z.1.Valid 53 2646 := by decide +kernel
private theorem fee53_073_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source073.plan.table+
      4*22976*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*345185388846 := by decide +kernel
private theorem range53From22485To2745 : Segment 53 22485 22976 2646 2745 :=
  paid (pc:=75) (v:=345185388846) (by decide) source073_valid tests53_073_2646 fee53_073_22976 (by decide +kernel)

private theorem tests53_069_2745 : ∀ z∈source069.plan.table,z.1.Valid 53 2745 := by decide +kernel
private theorem fee53_069_22976 :
    PopulationFees20258.bill (n:=22976) (PopulationFees20258.tabulate (22976-1) 256) source069.plan.table+
      4*22976*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*219847992896 := by decide +kernel
private theorem range53From22485To2757 : Segment 53 22485 22976 2745 2757 :=
  paid (pc:=75) (v:=219847992896) (by decide) source069_valid tests53_069_2745 fee53_069_22976 (by decide +kernel)

private theorem range53From22485 : Win 53 22485 22976 :=
  complete (by decide) (by decide) (join_population (join_population range53From22485To2384 (join_population range53From22485To2509 range53From22485To2591)) (join_population range53From22485To2646 (join_population range53From22485To2745 range53From22485To2757)))

private theorem fee53_057_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source057.plan.table+
      4*23541*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*190492396857 := by decide +kernel
private theorem range53From22977To2403 : Segment 53 22977 23541 0 2403 :=
  paid (pc:=78) (v:=190492396857) (by decide) source057_valid tests53_057_0 fee53_057_23541 (by decide +kernel)

private theorem tests53_060_2403 : ∀ z∈source060.plan.table,z.1.Valid 53 2403 := by decide +kernel
private theorem fee53_060_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source060.plan.table+
      4*23541*NaturalPopulation20258.weights source060.extras≤source060.plan.scale*219282679806 := by decide +kernel
private theorem range53From22977To2523 : Segment 53 22977 23541 2403 2523 :=
  paid (pc:=77) (v:=219282679806) (by decide) source060_valid tests53_060_2403 fee53_060_23541 (by decide +kernel)

private theorem tests53_068_2523 : ∀ z∈source068.plan.table,z.1.Valid 53 2523 := by decide +kernel
private theorem fee53_068_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source068.plan.table+
      4*23541*NaturalPopulation20258.weights source068.extras≤source068.plan.scale*262190293500 := by decide +kernel
private theorem range53From22977To2597 : Segment 53 22977 23541 2523 2597 :=
  paid (pc:=76) (v:=262190293500) (by decide) source068_valid tests53_068_2523 fee53_068_23541 (by decide +kernel)

private theorem tests53_072_2597 : ∀ z∈source072.plan.table,z.1.Valid 53 2597 := by decide +kernel
private theorem fee53_072_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source072.plan.table+
      4*23541*NaturalPopulation20258.weights source072.extras≤source072.plan.scale*313529322337 := by decide +kernel
private theorem range53From22977To2644 : Segment 53 22977 23541 2597 2644 :=
  paid (pc:=76) (v:=313529322337) (by decide) source072_valid tests53_072_2597 fee53_072_23541 (by decide +kernel)

private theorem tests53_073_2644 : ∀ z∈source073.plan.table,z.1.Valid 53 2644 := by decide +kernel
private theorem fee53_073_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source073.plan.table+
      4*23541*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*360784395252 := by decide +kernel
private theorem range53From22977To2731 : Segment 53 22977 23541 2644 2731 :=
  paid (pc:=75) (v:=360784395252) (by decide) source073_valid tests53_073_2644 fee53_073_23541 (by decide +kernel)

private theorem tests53_069_2731 : ∀ z∈source069.plan.table,z.1.Valid 53 2731 := by decide +kernel
private theorem fee53_069_23541 :
    PopulationFees20258.bill (n:=23541) (PopulationFees20258.tabulate (23541-1) 256) source069.plan.table+
      4*23541*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*230019105354 := by decide +kernel
private theorem range53From22977To2757 : Segment 53 22977 23541 2731 2757 :=
  paid (pc:=75) (v:=230019105354) (by decide) source069_valid tests53_069_2731 fee53_069_23541 (by decide +kernel)

private theorem range53From22977 : Win 53 22977 23541 :=
  complete (by decide) (by decide) (join_population (join_population range53From22977To2403 (join_population range53From22977To2523 range53From22977To2597)) (join_population range53From22977To2644 (join_population range53From22977To2731 range53From22977To2757)))

theorem cut53From22041 : Win 53 22041 23541 :=
  (join_ground range53From22041 (join_ground range53From22485 range53From22977))

end JSP233.FiniteCutRanges20258
