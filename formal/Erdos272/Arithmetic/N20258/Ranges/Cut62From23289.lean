module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source110

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests62_110_0 : ∀ z∈source110.plan.table,z.1.Valid 62 0 := by decide +kernel
private theorem fee62_110_23992 :
    PopulationFees20258.bill (n:=23992) (PopulationFees20258.tabulate (23992-1) 256) source110.plan.table+
      4*23992*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*222267379964 := by decide +kernel
private theorem range62From23289To3117 : Segment 62 23289 23992 0 3117 :=
  paid (pc:=72) (v:=222267379964) (by decide) source110_valid tests62_110_0 fee62_110_23992 (by decide +kernel)

private theorem tests62_110_3117 : ∀ z∈source110.plan.table,z.1.Valid 62 3117 := by decide +kernel
private theorem range62From23289To3145 : Segment 62 23289 23992 3117 3145 :=
  paid (pc:=72) (v:=222267379964) (by decide) source110_valid tests62_110_3117 fee62_110_23992 (by decide +kernel)

private theorem tests62_106_3145 : ∀ z∈source106.plan.table,z.1.Valid 62 3145 := by decide +kernel
private theorem fee62_106_23992 :
    PopulationFees20258.bill (n:=23992) (PopulationFees20258.tabulate (23992-1) 256) source106.plan.table+
      4*23992*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*339435499187 := by decide +kernel
private theorem range62From23289To3403 : Segment 62 23289 23992 3145 3403 :=
  paid (pc:=70) (v:=339435499187) (by decide) source106_valid tests62_106_3145 fee62_106_23992 (by decide +kernel)

private theorem tests62_105_3403 : ∀ z∈source105.plan.table,z.1.Valid 62 3403 := by decide +kernel
private theorem fee62_105_23992 :
    PopulationFees20258.bill (n:=23992) (PopulationFees20258.tabulate (23992-1) 256) source105.plan.table+
      4*23992*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*332800100886 := by decide +kernel
private theorem range62From23289To3471 : Segment 62 23289 23992 3403 3471 :=
  paid (pc:=69) (v:=332800100886) (by decide) source105_valid tests62_105_3403 fee62_105_23992 (by decide +kernel)

private theorem tests62_105_3471 : ∀ z∈source105.plan.table,z.1.Valid 62 3471 := by decide +kernel
private theorem range62From23289To3474 : Segment 62 23289 23992 3471 3474 :=
  paid (pc:=69) (v:=332800100886) (by decide) source105_valid tests62_105_3471 fee62_105_23992 (by decide +kernel)

private theorem tests62_108_3474 : ∀ z∈source108.plan.table,z.1.Valid 62 3474 := by decide +kernel
private theorem fee62_108_23992 :
    PopulationFees20258.bill (n:=23992) (PopulationFees20258.tabulate (23992-1) 256) source108.plan.table+
      4*23992*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*274220409349 := by decide +kernel
private theorem range62From23289To3783 : Segment 62 23289 23992 3474 3783 :=
  paid (pc:=66) (v:=274220409349) (by decide) source108_valid tests62_108_3474 fee62_108_23992 (by decide +kernel)

private theorem range62From23289 : Win 62 23289 23992 :=
  complete (by decide) (by decide) (join_population (join_population range62From23289To3117 (join_population range62From23289To3145 range62From23289To3403)) (join_population range62From23289To3471 (join_population range62From23289To3474 range62From23289To3783)))

private theorem fee62_110_24652 :
    PopulationFees20258.bill (n:=24652) (PopulationFees20258.tabulate (24652-1) 256) source110.plan.table+
      4*24652*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*233752245086 := by decide +kernel
private theorem range62From23993To3162 : Segment 62 23993 24652 0 3162 :=
  paid (pc:=73) (v:=233752245086) (by decide) source110_valid tests62_110_0 fee62_110_24652 (by decide +kernel)

private theorem tests62_105_3162 : ∀ z∈source105.plan.table,z.1.Valid 62 3162 := by decide +kernel
private theorem fee62_105_24652 :
    PopulationFees20258.bill (n:=24652) (PopulationFees20258.tabulate (24652-1) 256) source105.plan.table+
      4*24652*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*349836473465 := by decide +kernel
private theorem range62From23993To3463 : Segment 62 23993 24652 3162 3463 :=
  paid (pc:=70) (v:=349836473465) (by decide) source105_valid tests62_105_3162 fee62_105_24652 (by decide +kernel)

private theorem tests62_105_3463 : ∀ z∈source105.plan.table,z.1.Valid 62 3463 := by decide +kernel
private theorem range62From23993To3474 : Segment 62 23993 24652 3463 3474 :=
  paid (pc:=70) (v:=349836473465) (by decide) source105_valid tests62_105_3463 fee62_105_24652 (by decide +kernel)

private theorem fee62_108_24652 :
    PopulationFees20258.bill (n:=24652) (PopulationFees20258.tabulate (24652-1) 256) source108.plan.table+
      4*24652*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*288172321973 := by decide +kernel
private theorem range62From23993To3783 : Segment 62 23993 24652 3474 3783 :=
  paid (pc:=67) (v:=288172321973) (by decide) source108_valid tests62_108_3474 fee62_108_24652 (by decide +kernel)

private theorem range62From23993 : Win 62 23993 24652 :=
  complete (by decide) (by decide) (join_population (join_population range62From23993To3162 range62From23993To3463) (join_population range62From23993To3474 range62From23993To3783))

private theorem fee62_110_25300 :
    PopulationFees20258.bill (n:=25300) (PopulationFees20258.tabulate (25300-1) 256) source110.plan.table+
      4*25300*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*245084399784 := by decide +kernel
private theorem range62From24653To3199 : Segment 62 24653 25300 0 3199 :=
  paid (pc:=73) (v:=245084399784) (by decide) source110_valid tests62_110_0 fee62_110_25300 (by decide +kernel)

private theorem tests62_105_3199 : ∀ z∈source105.plan.table,z.1.Valid 62 3199 := by decide +kernel
private theorem fee62_105_25300 :
    PopulationFees20258.bill (n:=25300) (PopulationFees20258.tabulate (25300-1) 256) source105.plan.table+
      4*25300*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*366442028058 := by decide +kernel
private theorem range62From24653To3468 : Segment 62 24653 25300 3199 3468 :=
  paid (pc:=71) (v:=366442028058) (by decide) source105_valid tests62_105_3199 fee62_105_25300 (by decide +kernel)

private theorem tests62_105_3468 : ∀ z∈source105.plan.table,z.1.Valid 62 3468 := by decide +kernel
private theorem range62From24653To3476 : Segment 62 24653 25300 3468 3476 :=
  paid (pc:=71) (v:=366442028058) (by decide) source105_valid tests62_105_3468 fee62_105_25300 (by decide +kernel)

private theorem tests62_108_3476 : ∀ z∈source108.plan.table,z.1.Valid 62 3476 := by decide +kernel
private theorem fee62_108_25300 :
    PopulationFees20258.bill (n:=25300) (PopulationFees20258.tabulate (25300-1) 256) source108.plan.table+
      4*25300*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*302187716410 := by decide +kernel
private theorem range62From24653To3783 : Segment 62 24653 25300 3476 3783 :=
  paid (pc:=68) (v:=302187716410) (by decide) source108_valid tests62_108_3476 fee62_108_25300 (by decide +kernel)

private theorem range62From24653 : Win 62 24653 25300 :=
  complete (by decide) (by decide) (join_population (join_population range62From24653To3199 range62From24653To3468) (join_population range62From24653To3476 range62From24653To3783))

private theorem fee62_110_25956 :
    PopulationFees20258.bill (n:=25956) (PopulationFees20258.tabulate (25956-1) 256) source110.plan.table+
      4*25956*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*256910085054 := by decide +kernel
private theorem range62From25301To3229 : Segment 62 25301 25956 0 3229 :=
  paid (pc:=74) (v:=256910085054) (by decide) source110_valid tests62_110_0 fee62_110_25956 (by decide +kernel)

private theorem tests62_105_3229 : ∀ z∈source105.plan.table,z.1.Valid 62 3229 := by decide +kernel
private theorem fee62_105_25956 :
    PopulationFees20258.bill (n:=25956) (PopulationFees20258.tabulate (25956-1) 256) source105.plan.table+
      4*25956*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*383965506863 := by decide +kernel
private theorem range62From25301To3467 : Segment 62 25301 25956 3229 3467 :=
  paid (pc:=72) (v:=383965506863) (by decide) source105_valid tests62_105_3229 fee62_105_25956 (by decide +kernel)

private theorem tests62_105_3467 : ∀ z∈source105.plan.table,z.1.Valid 62 3467 := by decide +kernel
private theorem range62From25301To3475 : Segment 62 25301 25956 3467 3475 :=
  paid (pc:=72) (v:=383965506863) (by decide) source105_valid tests62_105_3467 fee62_105_25956 (by decide +kernel)

private theorem tests62_108_3475 : ∀ z∈source108.plan.table,z.1.Valid 62 3475 := by decide +kernel
private theorem fee62_108_25956 :
    PopulationFees20258.bill (n:=25956) (PopulationFees20258.tabulate (25956-1) 256) source108.plan.table+
      4*25956*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*316631164628 := by decide +kernel
private theorem range62From25301To3783 : Segment 62 25301 25956 3475 3783 :=
  paid (pc:=69) (v:=316631164628) (by decide) source108_valid tests62_108_3475 fee62_108_25956 (by decide +kernel)

private theorem range62From25301 : Win 62 25301 25956 :=
  complete (by decide) (by decide) (join_population (join_population range62From25301To3229 range62From25301To3467) (join_population range62From25301To3475 range62From25301To3783))

private theorem fee62_110_26636 :
    PopulationFees20258.bill (n:=26636) (PopulationFees20258.tabulate (26636-1) 256) source110.plan.table+
      4*26636*NaturalPopulation20258.weights source110.extras≤source110.plan.scale*269381287604 := by decide +kernel
private theorem range62From25957To3256 : Segment 62 25957 26636 0 3256 :=
  paid (pc:=74) (v:=269381287604) (by decide) source110_valid tests62_110_0 fee62_110_26636 (by decide +kernel)

private theorem tests62_105_3256 : ∀ z∈source105.plan.table,z.1.Valid 62 3256 := by decide +kernel
private theorem fee62_105_26636 :
    PopulationFees20258.bill (n:=26636) (PopulationFees20258.tabulate (26636-1) 256) source105.plan.table+
      4*26636*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*402586205702 := by decide +kernel
private theorem range62From25957To3468 : Segment 62 25957 26636 3256 3468 :=
  paid (pc:=73) (v:=402586205702) (by decide) source105_valid tests62_105_3256 fee62_105_26636 (by decide +kernel)

private theorem range62From25957To3474 : Segment 62 25957 26636 3468 3474 :=
  paid (pc:=73) (v:=402586205702) (by decide) source105_valid tests62_105_3468 fee62_105_26636 (by decide +kernel)

private theorem fee62_108_26636 :
    PopulationFees20258.bill (n:=26636) (PopulationFees20258.tabulate (26636-1) 256) source108.plan.table+
      4*26636*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*332218923922 := by decide +kernel
private theorem range62From25957To3783 : Segment 62 25957 26636 3474 3783 :=
  paid (pc:=70) (v:=332218923922) (by decide) source108_valid tests62_108_3474 fee62_108_26636 (by decide +kernel)

private theorem range62From25957 : Win 62 25957 26636 :=
  complete (by decide) (by decide) (join_population (join_population range62From25957To3256 range62From25957To3468) (join_population range62From25957To3474 range62From25957To3783))

theorem cut62From23289 : Win 62 23289 26636 :=
  (join_ground (join_ground range62From23289 range62From23993) (join_ground range62From24653 (join_ground range62From25301 range62From25957)))

end JSP233.FiniteCutRanges20258
