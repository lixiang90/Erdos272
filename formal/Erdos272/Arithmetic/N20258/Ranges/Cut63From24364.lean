module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source113

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests63_113_0 : ∀ z∈source113.plan.table,z.1.Valid 63 0 := by decide +kernel
private theorem fee63_113_24926 :
    PopulationFees20258.bill (n:=24926) (PopulationFees20258.tabulate (24926-1) 256) source113.plan.table+
      4*24926*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*277896124355 := by decide +kernel
private theorem range63From24364To3444 : Segment 63 24364 24926 0 3444 :=
  paid (pc:=71) (v:=277896124355) (by decide) source113_valid tests63_113_0 fee63_113_24926 (by decide +kernel)

private theorem tests63_105_3444 : ∀ z∈source105.plan.table,z.1.Valid 63 3444 := by decide +kernel
private theorem fee63_105_24926 :
    PopulationFees20258.bill (n:=24926) (PopulationFees20258.tabulate (24926-1) 256) source105.plan.table+
      4*24926*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*356664690830 := by decide +kernel
private theorem range63From24364To3527 : Segment 63 24364 24926 3444 3527 :=
  paid (pc:=71) (v:=356664690830) (by decide) source105_valid tests63_105_3444 fee63_105_24926 (by decide +kernel)

private theorem tests63_105_3527 : ∀ z∈source105.plan.table,z.1.Valid 63 3527 := by decide +kernel
private theorem range63From24364To3529 : Segment 63 24364 24926 3527 3529 :=
  paid (pc:=71) (v:=356664690830) (by decide) source105_valid tests63_105_3527 fee63_105_24926 (by decide +kernel)

private theorem tests63_108_3529 : ∀ z∈source108.plan.table,z.1.Valid 63 3529 := by decide +kernel
private theorem fee63_108_24926 :
    PopulationFees20258.bill (n:=24926) (PopulationFees20258.tabulate (24926-1) 256) source108.plan.table+
      4*24926*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*294113015114 := by decide +kernel
private theorem range63From24364To3907 : Segment 63 24364 24926 3529 3907 :=
  paid (pc:=68) (v:=294113015114) (by decide) source108_valid tests63_108_3529 fee63_108_24926 (by decide +kernel)

private theorem range63From24364 : Win 63 24364 24926 :=
  complete (by decide) (by decide) (join_population (join_population range63From24364To3444 range63From24364To3527) (join_population range63From24364To3529 range63From24364To3907))

private theorem fee63_113_25480 :
    PopulationFees20258.bill (n:=25480) (PopulationFees20258.tabulate (25480-1) 256) source113.plan.table+
      4*25480*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*289253131680 := by decide +kernel
private theorem range63From24927To3460 : Segment 63 24927 25480 0 3460 :=
  paid (pc:=72) (v:=289253131680) (by decide) source113_valid tests63_113_0 fee63_113_25480 (by decide +kernel)

private theorem tests63_105_3460 : ∀ z∈source105.plan.table,z.1.Valid 63 3460 := by decide +kernel
private theorem fee63_105_25480 :
    PopulationFees20258.bill (n:=25480) (PopulationFees20258.tabulate (25480-1) 256) source105.plan.table+
      4*25480*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*371286077647 := by decide +kernel
private theorem range63From24927To3527 : Segment 63 24927 25480 3460 3527 :=
  paid (pc:=72) (v:=371286077647) (by decide) source105_valid tests63_105_3460 fee63_105_25480 (by decide +kernel)

private theorem range63From24927To3529 : Segment 63 24927 25480 3527 3529 :=
  paid (pc:=72) (v:=371286077647) (by decide) source105_valid tests63_105_3527 fee63_105_25480 (by decide +kernel)

private theorem fee63_108_25480 :
    PopulationFees20258.bill (n:=25480) (PopulationFees20258.tabulate (25480-1) 256) source108.plan.table+
      4*25480*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*306059396586 := by decide +kernel
private theorem range63From24927To3907 : Segment 63 24927 25480 3529 3907 :=
  paid (pc:=68) (v:=306059396586) (by decide) source108_valid tests63_108_3529 fee63_108_25480 (by decide +kernel)

private theorem range63From24927 : Win 63 24927 25480 :=
  complete (by decide) (by decide) (join_population (join_population range63From24927To3460 range63From24927To3527) (join_population range63From24927To3529 range63From24927To3907))

private theorem fee63_113_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source113.plan.table+
      4*26040*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*301005068791 := by decide +kernel
private theorem range63From25481To3472 : Segment 63 25481 26040 0 3472 :=
  paid (pc:=72) (v:=301005068791) (by decide) source113_valid tests63_113_0 fee63_113_26040 (by decide +kernel)

private theorem tests63_105_3472 : ∀ z∈source105.plan.table,z.1.Valid 63 3472 := by decide +kernel
private theorem fee63_105_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source105.plan.table+
      4*26040*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*386164015031 := by decide +kernel
private theorem range63From25481To3528 : Segment 63 25481 26040 3472 3528 :=
  paid (pc:=72) (v:=386164015031) (by decide) source105_valid tests63_105_3472 fee63_105_26040 (by decide +kernel)

private theorem tests63_105_3528 : ∀ z∈source105.plan.table,z.1.Valid 63 3528 := by decide +kernel
private theorem range63From25481To3530 : Segment 63 25481 26040 3528 3530 :=
  paid (pc:=72) (v:=386164015031) (by decide) source105_valid tests63_105_3528 fee63_105_26040 (by decide +kernel)

private theorem tests63_108_3530 : ∀ z∈source108.plan.table,z.1.Valid 63 3530 := by decide +kernel
private theorem fee63_108_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source108.plan.table+
      4*26040*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*318633361830 := by decide +kernel
private theorem range63From25481To3907 : Segment 63 25481 26040 3530 3907 :=
  paid (pc:=69) (v:=318633361830) (by decide) source108_valid tests63_108_3530 fee63_108_26040 (by decide +kernel)

private theorem range63From25481 : Win 63 25481 26040 :=
  complete (by decide) (by decide) (join_population (join_population range63From25481To3472 range63From25481To3528) (join_population range63From25481To3530 range63From25481To3907))

private theorem fee63_113_26618 :
    PopulationFees20258.bill (n:=26618) (PopulationFees20258.tabulate (26618-1) 256) source113.plan.table+
      4*26618*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*313377543546 := by decide +kernel
private theorem range63From26041To3481 : Segment 63 26041 26618 0 3481 :=
  paid (pc:=73) (v:=313377543546) (by decide) source113_valid tests63_113_0 fee63_113_26618 (by decide +kernel)

private theorem tests63_105_3481 : ∀ z∈source105.plan.table,z.1.Valid 63 3481 := by decide +kernel
private theorem fee63_105_26618 :
    PopulationFees20258.bill (n:=26618) (PopulationFees20258.tabulate (26618-1) 256) source105.plan.table+
      4*26618*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*402008593635 := by decide +kernel
private theorem range63From26041To3529 : Segment 63 26041 26618 3481 3529 :=
  paid (pc:=73) (v:=402008593635) (by decide) source105_valid tests63_105_3481 fee63_105_26618 (by decide +kernel)

private theorem fee63_108_26618 :
    PopulationFees20258.bill (n:=26618) (PopulationFees20258.tabulate (26618-1) 256) source108.plan.table+
      4*26618*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*331780356660 := by decide +kernel
private theorem range63From26041To3907 : Segment 63 26041 26618 3529 3907 :=
  paid (pc:=70) (v:=331780356660) (by decide) source108_valid tests63_108_3529 fee63_108_26618 (by decide +kernel)

private theorem range63From26041 : Win 63 26041 26618 :=
  complete (by decide) (by decide) (join_population range63From26041To3481 (join_population range63From26041To3529 range63From26041To3907))

private theorem fee63_113_27226 :
    PopulationFees20258.bill (n:=27226) (PopulationFees20258.tabulate (27226-1) 256) source113.plan.table+
      4*27226*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*326801924565 := by decide +kernel
private theorem range63From26619To3491 : Segment 63 26619 27226 0 3491 :=
  paid (pc:=73) (v:=326801924565) (by decide) source113_valid tests63_113_0 fee63_113_27226 (by decide +kernel)

private theorem tests63_105_3491 : ∀ z∈source105.plan.table,z.1.Valid 63 3491 := by decide +kernel
private theorem fee63_105_27226 :
    PopulationFees20258.bill (n:=27226) (PopulationFees20258.tabulate (27226-1) 256) source105.plan.table+
      4*27226*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*419085810324 := by decide +kernel
private theorem range63From26619To3529 : Segment 63 26619 27226 3491 3529 :=
  paid (pc:=73) (v:=419085810324) (by decide) source105_valid tests63_105_3491 fee63_105_27226 (by decide +kernel)

private theorem fee63_108_27226 :
    PopulationFees20258.bill (n:=27226) (PopulationFees20258.tabulate (27226-1) 256) source108.plan.table+
      4*27226*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*345954792095 := by decide +kernel
private theorem range63From26619To3883 : Segment 63 26619 27226 3529 3883 :=
  paid (pc:=71) (v:=345954792095) (by decide) source108_valid tests63_108_3529 fee63_108_27226 (by decide +kernel)

private theorem tests63_112_3883 : ∀ z∈source112.plan.table,z.1.Valid 63 3883 := by decide +kernel
private theorem fee63_112_27226 :
    PopulationFees20258.bill (n:=27226) (PopulationFees20258.tabulate (27226-1) 256) source112.plan.table+
      4*27226*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*361587746806 := by decide +kernel
private theorem range63From26619To3907 : Segment 63 26619 27226 3883 3907 :=
  paid (pc:=69) (v:=361587746806) (by decide) source112_valid tests63_112_3883 fee63_112_27226 (by decide +kernel)

private theorem range63From26619 : Win 63 26619 27226 :=
  complete (by decide) (by decide) (join_population (join_population range63From26619To3491 range63From26619To3529) (join_population range63From26619To3883 range63From26619To3907))

private theorem fee63_113_27880 :
    PopulationFees20258.bill (n:=27880) (PopulationFees20258.tabulate (27880-1) 256) source113.plan.table+
      4*27880*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*341322123177 := by decide +kernel
private theorem range63From27227To3502 : Segment 63 27227 27880 0 3502 :=
  paid (pc:=74) (v:=341322123177) (by decide) source113_valid tests63_113_0 fee63_113_27880 (by decide +kernel)

private theorem tests63_105_3502 : ∀ z∈source105.plan.table,z.1.Valid 63 3502 := by decide +kernel
private theorem fee63_105_27880 :
    PopulationFees20258.bill (n:=27880) (PopulationFees20258.tabulate (27880-1) 256) source105.plan.table+
      4*27880*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*437612733850 := by decide +kernel
private theorem range63From27227To3529 : Segment 63 27227 27880 3502 3529 :=
  paid (pc:=74) (v:=437612733850) (by decide) source105_valid tests63_105_3502 fee63_105_27880 (by decide +kernel)

private theorem fee63_108_27880 :
    PopulationFees20258.bill (n:=27880) (PopulationFees20258.tabulate (27880-1) 256) source108.plan.table+
      4*27880*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*361488761145 := by decide +kernel
private theorem range63From27227To3863 : Segment 63 27227 27880 3529 3863 :=
  paid (pc:=71) (v:=361488761145) (by decide) source108_valid tests63_108_3529 fee63_108_27880 (by decide +kernel)

private theorem tests63_112_3863 : ∀ z∈source112.plan.table,z.1.Valid 63 3863 := by decide +kernel
private theorem fee63_112_27880 :
    PopulationFees20258.bill (n:=27880) (PopulationFees20258.tabulate (27880-1) 256) source112.plan.table+
      4*27880*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*377959519245 := by decide +kernel
private theorem range63From27227To3907 : Segment 63 27227 27880 3863 3907 :=
  paid (pc:=70) (v:=377959519245) (by decide) source112_valid tests63_112_3863 fee63_112_27880 (by decide +kernel)

private theorem range63From27227 : Win 63 27227 27880 :=
  complete (by decide) (by decide) (join_population (join_population range63From27227To3502 range63From27227To3529) (join_population range63From27227To3863 range63From27227To3907))

theorem cut63From24364 : Win 63 24364 27880 :=
  (join_ground (join_ground range63From24364 (join_ground range63From24927 range63From25481)) (join_ground range63From26041 (join_ground range63From26619 range63From27227)))

end JSP233.FiniteCutRanges20258
