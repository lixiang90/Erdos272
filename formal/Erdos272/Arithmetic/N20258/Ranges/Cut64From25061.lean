module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source114

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests64_114_0 : ∀ z∈source114.plan.table,z.1.Valid 64 0 := by decide +kernel
private theorem fee64_114_25674 :
    PopulationFees20258.bill (n:=25674) (PopulationFees20258.tabulate (25674-1) 256) source114.plan.table+
      4*25674*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*271168201316 := by decide +kernel
private theorem range64From25061To3546 : Segment 64 25061 25674 0 3546 :=
  paid (pc:=71) (v:=271168201316) (by decide) source114_valid tests64_114_0 fee64_114_25674 (by decide +kernel)

private theorem tests64_114_3546 : ∀ z∈source114.plan.table,z.1.Valid 64 3546 := by decide +kernel
private theorem range64From25061To3584 : Segment 64 25061 25674 3546 3584 :=
  paid (pc:=71) (v:=271168201316) (by decide) source114_valid tests64_114_3546 fee64_114_25674 (by decide +kernel)

private theorem tests64_108_3584 : ∀ z∈source108.plan.table,z.1.Valid 64 3584 := by decide +kernel
private theorem fee64_108_25674 :
    PopulationFees20258.bill (n:=25674) (PopulationFees20258.tabulate (25674-1) 256) source108.plan.table+
      4*25674*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*310550789968 := by decide +kernel
private theorem range64From25061To3920 : Segment 64 25061 25674 3584 3920 :=
  paid (pc:=68) (v:=310550789968) (by decide) source108_valid tests64_108_3584 fee64_108_25674 (by decide +kernel)

private theorem tests64_112_3920 : ∀ z∈source112.plan.table,z.1.Valid 64 3920 := by decide +kernel
private theorem fee64_112_25674 :
    PopulationFees20258.bill (n:=25674) (PopulationFees20258.tabulate (25674-1) 256) source112.plan.table+
      4*25674*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*324547037998 := by decide +kernel
private theorem range64From25061To4033 : Segment 64 25061 25674 3920 4033 :=
  paid (pc:=66) (v:=324547037998) (by decide) source112_valid tests64_112_3920 fee64_112_25674 (by decide +kernel)

private theorem range64From25061 : Win 64 25061 25674 :=
  complete (by decide) (by decide) (join_population (join_population range64From25061To3546 range64From25061To3584) (join_population range64From25061To3920 range64From25061To4033))

private theorem fee64_114_26309 :
    PopulationFees20258.bill (n:=26309) (PopulationFees20258.tabulate (26309-1) 256) source114.plan.table+
      4*26309*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*283551593816 := by decide +kernel
private theorem range64From25675To3550 : Segment 64 25675 26309 0 3550 :=
  paid (pc:=72) (v:=283551593816) (by decide) source114_valid tests64_114_0 fee64_114_26309 (by decide +kernel)

private theorem tests64_114_3550 : ∀ z∈source114.plan.table,z.1.Valid 64 3550 := by decide +kernel
private theorem range64From25675To3584 : Segment 64 25675 26309 3550 3584 :=
  paid (pc:=72) (v:=283551593816) (by decide) source114_valid tests64_114_3550 fee64_114_26309 (by decide +kernel)

private theorem fee64_108_26309 :
    PopulationFees20258.bill (n:=26309) (PopulationFees20258.tabulate (26309-1) 256) source108.plan.table+
      4*26309*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*324586649442 := by decide +kernel
private theorem range64From25675To3883 : Segment 64 25675 26309 3584 3883 :=
  paid (pc:=69) (v:=324586649442) (by decide) source108_valid tests64_108_3584 fee64_108_26309 (by decide +kernel)

private theorem tests64_112_3883 : ∀ z∈source112.plan.table,z.1.Valid 64 3883 := by decide +kernel
private theorem fee64_112_26309 :
    PopulationFees20258.bill (n:=26309) (PopulationFees20258.tabulate (26309-1) 256) source112.plan.table+
      4*26309*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*339525836731 := by decide +kernel
private theorem range64From25675To4033 : Segment 64 25675 26309 3883 4033 :=
  paid (pc:=67) (v:=339525836731) (by decide) source112_valid tests64_112_3883 fee64_112_26309 (by decide +kernel)

private theorem range64From25675 : Win 64 25675 26309 :=
  complete (by decide) (by decide) (join_population (join_population range64From25675To3550 range64From25675To3584) (join_population range64From25675To3883 range64From25675To4033))

private theorem fee64_114_26980 :
    PopulationFees20258.bill (n:=26980) (PopulationFees20258.tabulate (26980-1) 256) source114.plan.table+
      4*26980*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*297139879433 := by decide +kernel
private theorem range64From26310To3553 : Segment 64 26310 26980 0 3553 :=
  paid (pc:=72) (v:=297139879433) (by decide) source114_valid tests64_114_0 fee64_114_26980 (by decide +kernel)

private theorem tests64_114_3553 : ∀ z∈source114.plan.table,z.1.Valid 64 3553 := by decide +kernel
private theorem range64From26310To3584 : Segment 64 26310 26980 3553 3584 :=
  paid (pc:=72) (v:=297139879433) (by decide) source114_valid tests64_114_3553 fee64_114_26980 (by decide +kernel)

private theorem fee64_108_26980 :
    PopulationFees20258.bill (n:=26980) (PopulationFees20258.tabulate (26980-1) 256) source108.plan.table+
      4*26980*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*340251998257 := by decide +kernel
private theorem range64From26310To3850 : Segment 64 26310 26980 3584 3850 :=
  paid (pc:=70) (v:=340251998257) (by decide) source108_valid tests64_108_3584 fee64_108_26980 (by decide +kernel)

private theorem tests64_112_3850 : ∀ z∈source112.plan.table,z.1.Valid 64 3850 := by decide +kernel
private theorem fee64_112_26980 :
    PopulationFees20258.bill (n:=26980) (PopulationFees20258.tabulate (26980-1) 256) source112.plan.table+
      4*26980*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*355694278088 := by decide +kernel
private theorem range64From26310To4033 : Segment 64 26310 26980 3850 4033 :=
  paid (pc:=68) (v:=355694278088) (by decide) source112_valid tests64_112_3850 fee64_112_26980 (by decide +kernel)

private theorem range64From26310 : Win 64 26310 26980 :=
  complete (by decide) (by decide) (join_population (join_population range64From26310To3553 range64From26310To3584) (join_population range64From26310To3850 range64From26310To4033))

private theorem fee64_114_27708 :
    PopulationFees20258.bill (n:=27708) (PopulationFees20258.tabulate (27708-1) 256) source114.plan.table+
      4*27708*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*311884620845 := by decide +kernel
private theorem range64From26981To3556 : Segment 64 26981 27708 0 3556 :=
  paid (pc:=73) (v:=311884620845) (by decide) source114_valid tests64_114_0 fee64_114_27708 (by decide +kernel)

private theorem tests64_114_3556 : ∀ z∈source114.plan.table,z.1.Valid 64 3556 := by decide +kernel
private theorem range64From26981To3584 : Segment 64 26981 27708 3556 3584 :=
  paid (pc:=73) (v:=311884620845) (by decide) source114_valid tests64_114_3556 fee64_114_27708 (by decide +kernel)

private theorem fee64_108_27708 :
    PopulationFees20258.bill (n:=27708) (PopulationFees20258.tabulate (27708-1) 256) source108.plan.table+
      4*27708*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*357241634119 := by decide +kernel
private theorem range64From26981To3823 : Segment 64 26981 27708 3584 3823 :=
  paid (pc:=71) (v:=357241634119) (by decide) source108_valid tests64_108_3584 fee64_108_27708 (by decide +kernel)

private theorem tests64_112_3823 : ∀ z∈source112.plan.table,z.1.Valid 64 3823 := by decide +kernel
private theorem fee64_112_27708 :
    PopulationFees20258.bill (n:=27708) (PopulationFees20258.tabulate (27708-1) 256) source112.plan.table+
      4*27708*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*373469502120 := by decide +kernel
private theorem range64From26981To4033 : Segment 64 26981 27708 3823 4033 :=
  paid (pc:=69) (v:=373469502120) (by decide) source112_valid tests64_112_3823 fee64_112_27708 (by decide +kernel)

private theorem range64From26981 : Win 64 26981 27708 :=
  complete (by decide) (by decide) (join_population (join_population range64From26981To3556 range64From26981To3584) (join_population range64From26981To3823 range64From26981To4033))

private theorem fee64_114_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source114.plan.table+
      4*28512*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*328751382027 := by decide +kernel
private theorem range64From27709To3559 : Segment 64 27709 28512 0 3559 :=
  paid (pc:=73) (v:=328751382027) (by decide) source114_valid tests64_114_0 fee64_114_28512 (by decide +kernel)

private theorem tests64_114_3559 : ∀ z∈source114.plan.table,z.1.Valid 64 3559 := by decide +kernel
private theorem range64From27709To3585 : Segment 64 27709 28512 3559 3585 :=
  paid (pc:=73) (v:=328751382027) (by decide) source114_valid tests64_114_3559 fee64_114_28512 (by decide +kernel)

private theorem tests64_108_3585 : ∀ z∈source108.plan.table,z.1.Valid 64 3585 := by decide +kernel
private theorem fee64_108_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source108.plan.table+
      4*28512*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*376743631838 := by decide +kernel
private theorem range64From27709To3798 : Segment 64 27709 28512 3585 3798 :=
  paid (pc:=72) (v:=376743631838) (by decide) source108_valid tests64_108_3585 fee64_108_28512 (by decide +kernel)

private theorem tests64_112_3798 : ∀ z∈source112.plan.table,z.1.Valid 64 3798 := by decide +kernel
private theorem fee64_112_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source112.plan.table+
      4*28512*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*394001100698 := by decide +kernel
private theorem range64From27709To4033 : Segment 64 27709 28512 3798 4033 :=
  paid (pc:=69) (v:=394001100698) (by decide) source112_valid tests64_112_3798 fee64_112_28512 (by decide +kernel)

private theorem range64From27709 : Win 64 27709 28512 :=
  complete (by decide) (by decide) (join_population (join_population range64From27709To3559 range64From27709To3585) (join_population range64From27709To3798 range64From27709To4033))

private theorem fee64_114_29418 :
    PopulationFees20258.bill (n:=29418) (PopulationFees20258.tabulate (29418-1) 256) source114.plan.table+
      4*29418*NaturalPopulation20258.weights source114.extras≤source114.plan.scale*348599337754 := by decide +kernel
private theorem range64From28513To3560 : Segment 64 28513 29418 0 3560 :=
  paid (pc:=73) (v:=348599337754) (by decide) source114_valid tests64_114_0 fee64_114_29418 (by decide +kernel)

private theorem tests64_114_3560 : ∀ z∈source114.plan.table,z.1.Valid 64 3560 := by decide +kernel
private theorem range64From28513To3584 : Segment 64 28513 29418 3560 3584 :=
  paid (pc:=73) (v:=348599337754) (by decide) source114_valid tests64_114_3560 fee64_114_29418 (by decide +kernel)

private theorem fee64_108_29418 :
    PopulationFees20258.bill (n:=29418) (PopulationFees20258.tabulate (29418-1) 256) source108.plan.table+
      4*29418*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*399360705159 := by decide +kernel
private theorem range64From28513To3775 : Segment 64 28513 29418 3584 3775 :=
  paid (pc:=72) (v:=399360705159) (by decide) source108_valid tests64_108_3584 fee64_108_29418 (by decide +kernel)

private theorem tests64_112_3775 : ∀ z∈source112.plan.table,z.1.Valid 64 3775 := by decide +kernel
private theorem fee64_112_29418 :
    PopulationFees20258.bill (n:=29418) (PopulationFees20258.tabulate (29418-1) 256) source112.plan.table+
      4*29418*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*417543247207 := by decide +kernel
private theorem range64From28513To4033 : Segment 64 28513 29418 3775 4033 :=
  paid (pc:=70) (v:=417543247207) (by decide) source112_valid tests64_112_3775 fee64_112_29418 (by decide +kernel)

private theorem range64From28513 : Win 64 28513 29418 :=
  complete (by decide) (by decide) (join_population (join_population range64From28513To3560 range64From28513To3584) (join_population range64From28513To3775 range64From28513To4033))

theorem cut64From25061 : Win 64 25061 29418 :=
  (join_ground (join_ground range64From25061 (join_ground range64From25675 range64From26310)) (join_ground range64From26981 (join_ground range64From27709 range64From28513)))

end JSP233.FiniteCutRanges20258
