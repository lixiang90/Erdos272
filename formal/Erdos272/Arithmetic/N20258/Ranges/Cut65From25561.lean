module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source109
public import Erdos272.Arithmetic.N20258.Sources.Source111
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source115
public import Erdos272.Arithmetic.N20258.Sources.Source116

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests65_115_0 : ∀ z∈source115.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_115_26238 :
    PopulationFees20258.bill (n:=26238) (PopulationFees20258.tabulate (26238-1) 256) source115.plan.table+
      4*26238*NaturalPopulation20258.weights source115.extras≤source115.plan.scale*266264858480 := by decide +kernel
private theorem range65From25561To3604 : Segment 65 25561 26238 0 3604 :=
  paid (pc:=71) (v:=266264858480) (by decide) source115_valid tests65_115_0 fee65_115_26238 (by decide +kernel)

private theorem tests65_115_3604 : ∀ z∈source115.plan.table,z.1.Valid 65 3604 := by decide +kernel
private theorem range65From25561To3639 : Segment 65 25561 26238 3604 3639 :=
  paid (pc:=71) (v:=266264858480) (by decide) source115_valid tests65_115_3604 fee65_115_26238 (by decide +kernel)

private theorem tests65_108_3639 : ∀ z∈source108.plan.table,z.1.Valid 65 3639 := by decide +kernel
private theorem fee65_108_26238 :
    PopulationFees20258.bill (n:=26238) (PopulationFees20258.tabulate (26238-1) 256) source108.plan.table+
      4*26238*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*323195668567 := by decide +kernel
private theorem range65From25561To3858 : Segment 65 25561 26238 3639 3858 :=
  paid (pc:=69) (v:=323195668567) (by decide) source108_valid tests65_108_3639 fee65_108_26238 (by decide +kernel)

private theorem tests65_112_3858 : ∀ z∈source112.plan.table,z.1.Valid 65 3858 := by decide +kernel
private theorem fee65_112_26238 :
    PopulationFees20258.bill (n:=26238) (PopulationFees20258.tabulate (26238-1) 256) source112.plan.table+
      4*26238*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*337971953156 := by decide +kernel
private theorem range65From25561To4161 : Segment 65 25561 26238 3858 4161 :=
  paid (pc:=66) (v:=337971953156) (by decide) source112_valid tests65_112_3858 fee65_112_26238 (by decide +kernel)

private theorem range65From25561 : Win 65 25561 26238 :=
  complete (by decide) (by decide) (join_population (join_population range65From25561To3604 range65From25561To3639) (join_population range65From25561To3858 range65From25561To4161))

private theorem tests65_116_0 : ∀ z∈source116.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_116_26945 :
    PopulationFees20258.bill (n:=26945) (PopulationFees20258.tabulate (26945-1) 256) source116.plan.table+
      4*26945*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*279518228458 := by decide +kernel
private theorem range65From26239To3607 : Segment 65 26239 26945 0 3607 :=
  paid (pc:=72) (v:=279518228458) (by decide) source116_valid tests65_116_0 fee65_116_26945 (by decide +kernel)

private theorem tests65_116_3607 : ∀ z∈source116.plan.table,z.1.Valid 65 3607 := by decide +kernel
private theorem range65From26239To3639 : Segment 65 26239 26945 3607 3639 :=
  paid (pc:=72) (v:=279518228458) (by decide) source116_valid tests65_116_3607 fee65_116_26945 (by decide +kernel)

private theorem fee65_108_26945 :
    PopulationFees20258.bill (n:=26945) (PopulationFees20258.tabulate (26945-1) 256) source108.plan.table+
      4*26945*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*339360150175 := by decide +kernel
private theorem range65From26239To3830 : Segment 65 26239 26945 3639 3830 :=
  paid (pc:=70) (v:=339360150175) (by decide) source108_valid tests65_108_3639 fee65_108_26945 (by decide +kernel)

private theorem tests65_112_3830 : ∀ z∈source112.plan.table,z.1.Valid 65 3830 := by decide +kernel
private theorem fee65_112_26945 :
    PopulationFees20258.bill (n:=26945) (PopulationFees20258.tabulate (26945-1) 256) source112.plan.table+
      4*26945*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*354890447745 := by decide +kernel
private theorem range65From26239To4161 : Segment 65 26239 26945 3830 4161 :=
  paid (pc:=67) (v:=354890447745) (by decide) source112_valid tests65_112_3830 fee65_112_26945 (by decide +kernel)

private theorem range65From26239 : Win 65 26239 26945 :=
  complete (by decide) (by decide) (join_population (join_population range65From26239To3607 range65From26239To3639) (join_population range65From26239To3830 range65From26239To4161))

private theorem fee65_115_27702 :
    PopulationFees20258.bill (n:=27702) (PopulationFees20258.tabulate (27702-1) 256) source115.plan.table+
      4*27702*NaturalPopulation20258.weights source115.extras≤source115.plan.scale*294221691728 := by decide +kernel
private theorem range65From26946To3610 : Segment 65 26946 27702 0 3610 :=
  paid (pc:=72) (v:=294221691728) (by decide) source115_valid tests65_115_0 fee65_115_27702 (by decide +kernel)

private theorem tests65_115_3610 : ∀ z∈source115.plan.table,z.1.Valid 65 3610 := by decide +kernel
private theorem range65From26946To3639 : Segment 65 26946 27702 3610 3639 :=
  paid (pc:=72) (v:=294221691728) (by decide) source115_valid tests65_115_3610 fee65_115_27702 (by decide +kernel)

private theorem fee65_108_27702 :
    PopulationFees20258.bill (n:=27702) (PopulationFees20258.tabulate (27702-1) 256) source108.plan.table+
      4*27702*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*357070207126 := by decide +kernel
private theorem range65From26946To3806 : Segment 65 26946 27702 3639 3806 :=
  paid (pc:=71) (v:=357070207126) (by decide) source108_valid tests65_108_3639 fee65_108_27702 (by decide +kernel)

private theorem tests65_111_3806 : ∀ z∈source111.plan.table,z.1.Valid 65 3806 := by decide +kernel
private theorem fee65_111_27702 :
    PopulationFees20258.bill (n:=27702) (PopulationFees20258.tabulate (27702-1) 256) source111.plan.table+
      4*27702*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*380199863799 := by decide +kernel
private theorem range65From26946To4161 : Segment 65 26946 27702 3806 4161 :=
  paid (pc:=68) (v:=380199863799) (by decide) source111_valid tests65_111_3806 fee65_111_27702 (by decide +kernel)

private theorem range65From26946 : Win 65 26946 27702 :=
  complete (by decide) (by decide) (join_population (join_population range65From26946To3610 range65From26946To3639) (join_population range65From26946To3806 range65From26946To4161))

private theorem fee65_116_28530 :
    PopulationFees20258.bill (n:=28530) (PopulationFees20258.tabulate (28530-1) 256) source116.plan.table+
      4*28530*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*310689034316 := by decide +kernel
private theorem range65From27703To3613 : Segment 65 27703 28530 0 3613 :=
  paid (pc:=73) (v:=310689034316) (by decide) source116_valid tests65_116_0 fee65_116_28530 (by decide +kernel)

private theorem tests65_116_3613 : ∀ z∈source116.plan.table,z.1.Valid 65 3613 := by decide +kernel
private theorem range65From27703To3639 : Segment 65 27703 28530 3613 3639 :=
  paid (pc:=73) (v:=310689034316) (by decide) source116_valid tests65_116_3613 fee65_116_28530 (by decide +kernel)

private theorem fee65_108_28530 :
    PopulationFees20258.bill (n:=28530) (PopulationFees20258.tabulate (28530-1) 256) source108.plan.table+
      4*28530*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*377159867101 := by decide +kernel
private theorem range65From27703To3784 : Segment 65 27703 28530 3639 3784 :=
  paid (pc:=72) (v:=377159867101) (by decide) source108_valid tests65_108_3639 fee65_108_28530 (by decide +kernel)

private theorem tests65_111_3784 : ∀ z∈source111.plan.table,z.1.Valid 65 3784 := by decide +kernel
private theorem fee65_111_28530 :
    PopulationFees20258.bill (n:=28530) (PopulationFees20258.tabulate (28530-1) 256) source111.plan.table+
      4*28530*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*401493153061 := by decide +kernel
private theorem range65From27703To4161 : Segment 65 27703 28530 3784 4161 :=
  paid (pc:=69) (v:=401493153061) (by decide) source111_valid tests65_111_3784 fee65_111_28530 (by decide +kernel)

private theorem range65From27703 : Win 65 27703 28530 :=
  complete (by decide) (by decide) (join_population (join_population range65From27703To3613 range65From27703To3639) (join_population range65From27703To3784 range65From27703To4161))

private theorem fee65_116_29460 :
    PopulationFees20258.bill (n:=29460) (PopulationFees20258.tabulate (29460-1) 256) source116.plan.table+
      4*29460*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*329691543960 := by decide +kernel
private theorem range65From28531To3615 : Segment 65 28531 29460 0 3615 :=
  paid (pc:=73) (v:=329691543960) (by decide) source116_valid tests65_116_0 fee65_116_29460 (by decide +kernel)

private theorem tests65_116_3615 : ∀ z∈source116.plan.table,z.1.Valid 65 3615 := by decide +kernel
private theorem range65From28531To3639 : Segment 65 28531 29460 3615 3639 :=
  paid (pc:=73) (v:=329691543960) (by decide) source116_valid tests65_116_3615 fee65_116_29460 (by decide +kernel)

private theorem fee65_108_29460 :
    PopulationFees20258.bill (n:=29460) (PopulationFees20258.tabulate (29460-1) 256) source108.plan.table+
      4*29460*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*400260225078 := by decide +kernel
private theorem range65From28531To3764 : Segment 65 28531 29460 3639 3764 :=
  paid (pc:=72) (v:=400260225078) (by decide) source108_valid tests65_108_3639 fee65_108_29460 (by decide +kernel)

private theorem tests65_109_3764 : ∀ z∈source109.plan.table,z.1.Valid 65 3764 := by decide +kernel
private theorem fee65_109_29460 :
    PopulationFees20258.bill (n:=29460) (PopulationFees20258.tabulate (29460-1) 256) source109.plan.table+
      4*29460*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*396329926186 := by decide +kernel
private theorem range65From28531To3782 : Segment 65 28531 29460 3764 3782 :=
  paid (pc:=72) (v:=396329926186) (by decide) source109_valid tests65_109_3764 fee65_109_29460 (by decide +kernel)

private theorem tests65_111_3782 : ∀ z∈source111.plan.table,z.1.Valid 65 3782 := by decide +kernel
private theorem fee65_111_29460 :
    PopulationFees20258.bill (n:=29460) (PopulationFees20258.tabulate (29460-1) 256) source111.plan.table+
      4*29460*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*425989443584 := by decide +kernel
private theorem range65From28531To4127 : Segment 65 28531 29460 3782 4127 :=
  paid (pc:=70) (v:=425989443584) (by decide) source111_valid tests65_111_3782 fee65_111_29460 (by decide +kernel)

private theorem tests65_112_4127 : ∀ z∈source112.plan.table,z.1.Valid 65 4127 := by decide +kernel
private theorem fee65_112_29460 :
    PopulationFees20258.bill (n:=29460) (PopulationFees20258.tabulate (29460-1) 256) source112.plan.table+
      4*29460*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*418406025236 := by decide +kernel
private theorem range65From28531To4161 : Segment 65 28531 29460 4127 4161 :=
  paid (pc:=70) (v:=418406025236) (by decide) source112_valid tests65_112_4127 fee65_112_29460 (by decide +kernel)

private theorem range65From28531 : Win 65 28531 29460 :=
  complete (by decide) (by decide) (join_population (join_population range65From28531To3615 (join_population range65From28531To3639 range65From28531To3764)) (join_population range65From28531To3782 (join_population range65From28531To4127 range65From28531To4161)))

theorem cut65From25561 : Win 65 25561 29460 :=
  (join_ground (join_ground range65From25561 range65From26239) (join_ground range65From26946 (join_ground range65From27703 range65From28531)))

end JSP233.FiniteCutRanges20258
