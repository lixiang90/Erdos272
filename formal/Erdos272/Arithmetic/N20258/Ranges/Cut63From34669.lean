module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source109
public import Erdos272.Arithmetic.N20258.Sources.Source111
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source113

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests63_113_0 : ∀ z∈source113.plan.table,z.1.Valid 63 0 := by decide +kernel
private theorem fee63_113_36824 :
    PopulationFees20258.bill (n:=36824) (PopulationFees20258.tabulate (36824-1) 256) source113.plan.table+
      4*36824*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*572185334384 := by decide +kernel
private theorem range63From34669To3521 : Segment 63 34669 36824 0 3521 :=
  paid (pc:=74) (v:=572185334384) (by decide) source113_valid tests63_113_0 fee63_113_36824 (by decide +kernel)

private theorem tests63_113_3521 : ∀ z∈source113.plan.table,z.1.Valid 63 3521 := by decide +kernel
private theorem range63From34669To3529 : Segment 63 34669 36824 3521 3529 :=
  paid (pc:=74) (v:=572185334384) (by decide) source113_valid tests63_113_3521 fee63_113_36824 (by decide +kernel)

private theorem tests63_108_3529 : ∀ z∈source108.plan.table,z.1.Valid 63 3529 := by decide +kernel
private theorem fee63_108_36824 :
    PopulationFees20258.bill (n:=36824) (PopulationFees20258.tabulate (36824-1) 256) source108.plan.table+
      4*36824*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*607580760336 := by decide +kernel
private theorem range63From34669To3693 : Segment 63 34669 36824 3529 3693 :=
  paid (pc:=74) (v:=607580760336) (by decide) source108_valid tests63_108_3529 fee63_108_36824 (by decide +kernel)

private theorem tests63_111_3693 : ∀ z∈source111.plan.table,z.1.Valid 63 3693 := by decide +kernel
private theorem fee63_111_36824 :
    PopulationFees20258.bill (n:=36824) (PopulationFees20258.tabulate (36824-1) 256) source111.plan.table+
      4*36824*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*646243314630 := by decide +kernel
private theorem range63From34669To3882 : Segment 63 34669 36824 3693 3882 :=
  paid (pc:=73) (v:=646243314630) (by decide) source111_valid tests63_111_3693 fee63_111_36824 (by decide +kernel)

private theorem tests63_112_3882 : ∀ z∈source112.plan.table,z.1.Valid 63 3882 := by decide +kernel
private theorem fee63_112_36824 :
    PopulationFees20258.bill (n:=36824) (PopulationFees20258.tabulate (36824-1) 256) source112.plan.table+
      4*36824*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*635080366144 := by decide +kernel
private theorem range63From34669To3907 : Segment 63 34669 36824 3882 3907 :=
  paid (pc:=72) (v:=635080366144) (by decide) source112_valid tests63_112_3882 fee63_112_36824 (by decide +kernel)

private theorem range63From34669 : Win 63 34669 36824 :=
  complete (by decide) (by decide) (join_population (join_population range63From34669To3521 range63From34669To3529) (join_population range63From34669To3693 (join_population range63From34669To3882 range63From34669To3907)))

private theorem fee63_113_39448 :
    PopulationFees20258.bill (n:=39448) (PopulationFees20258.tabulate (39448-1) 256) source113.plan.table+
      4*39448*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*651211826179 := by decide +kernel
private theorem range63From36825To3570 : Segment 63 36825 39448 0 3570 :=
  paid (pc:=74) (v:=651211826179) (by decide) source113_valid tests63_113_0 fee63_113_39448 (by decide +kernel)

private theorem tests63_109_3570 : ∀ z∈source109.plan.table,z.1.Valid 63 3570 := by decide +kernel
private theorem fee63_109_39448 :
    PopulationFees20258.bill (n:=39448) (PopulationFees20258.tabulate (39448-1) 256) source109.plan.table+
      4*39448*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*685371820585 := by decide +kernel
private theorem range63From36825To3729 : Segment 63 36825 39448 3570 3729 :=
  paid (pc:=74) (v:=685371820585) (by decide) source109_valid tests63_109_3570 fee63_109_39448 (by decide +kernel)

private theorem tests63_112_3729 : ∀ z∈source112.plan.table,z.1.Valid 63 3729 := by decide +kernel
private theorem fee63_112_39448 :
    PopulationFees20258.bill (n:=39448) (PopulationFees20258.tabulate (39448-1) 256) source112.plan.table+
      4*39448*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*723194789499 := by decide +kernel
private theorem range63From36825To3904 : Segment 63 36825 39448 3729 3904 :=
  paid (pc:=73) (v:=723194789499) (by decide) source112_valid tests63_112_3729 fee63_112_39448 (by decide +kernel)

private theorem tests63_112_3904 : ∀ z∈source112.plan.table,z.1.Valid 63 3904 := by decide +kernel
private theorem range63From36825To3907 : Segment 63 36825 39448 3904 3907 :=
  paid (pc:=73) (v:=723194789499) (by decide) source112_valid tests63_112_3904 fee63_112_39448 (by decide +kernel)

private theorem range63From36825 : Win 63 36825 39448 :=
  complete (by decide) (by decide) (join_population (join_population range63From36825To3570 range63From36825To3729) (join_population range63From36825To3904 range63From36825To3907))

private theorem range63From39449Price : ( .marked ⟨63,172,26,9000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range63From39449 : Win 63 39449 39999 :=
  classical_route (pc:=80) range63From39449Price (by decide +kernel)

theorem cut63From34669 : Win 63 34669 39999 :=
  (join_ground range63From34669 (join_ground range63From36825 range63From39449))

end JSP233.FiniteCutRanges20258
