module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source104
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests60_104_0 : ∀ z∈source104.plan.table,z.1.Valid 60 0 := by decide +kernel
private theorem fee60_104_25150 :
    PopulationFees20258.bill (n:=25150) (PopulationFees20258.tabulate (25150-1) 256) source104.plan.table+
      4*25150*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*220843340506 := by decide +kernel
private theorem range60From24593To2998 : Segment 60 24593 25150 0 2998 :=
  paid (pc:=75) (v:=220843340506) (by decide) source104_valid tests60_104_0 fee60_104_25150 (by decide +kernel)

private theorem tests60_102_2998 : ∀ z∈source102.plan.table,z.1.Valid 60 2998 := by decide +kernel
private theorem fee60_102_25150 :
    PopulationFees20258.bill (n:=25150) (PopulationFees20258.tabulate (25150-1) 256) source102.plan.table+
      4*25150*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*324168709012 := by decide +kernel
private theorem range60From24593To3252 : Segment 60 24593 25150 2998 3252 :=
  paid (pc:=73) (v:=324168709012) (by decide) source102_valid tests60_102_2998 fee60_102_25150 (by decide +kernel)

private theorem tests60_105_3252 : ∀ z∈source105.plan.table,z.1.Valid 60 3252 := by decide +kernel
private theorem fee60_105_25150 :
    PopulationFees20258.bill (n:=25150) (PopulationFees20258.tabulate (25150-1) 256) source105.plan.table+
      4*25150*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*362537878603 := by decide +kernel
private theorem range60From24593To3533 : Segment 60 24593 25150 3252 3533 :=
  paid (pc:=71) (v:=362537878603) (by decide) source105_valid tests60_105_3252 fee60_105_25150 (by decide +kernel)

private theorem tests60_105_3533 : ∀ z∈source105.plan.table,z.1.Valid 60 3533 := by decide +kernel
private theorem range60From24593To3541 : Segment 60 24593 25150 3533 3541 :=
  paid (pc:=71) (v:=362537878603) (by decide) source105_valid tests60_105_3533 fee60_105_25150 (by decide +kernel)

private theorem range60From24593 : Win 60 24593 25150 :=
  complete (by decide) (by decide) (join_population (join_population range60From24593To2998 range60From24593To3252) (join_population range60From24593To3533 range60From24593To3541))

private theorem fee60_104_25704 :
    PopulationFees20258.bill (n:=25704) (PopulationFees20258.tabulate (25704-1) 256) source104.plan.table+
      4*25704*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*229952155014 := by decide +kernel
private theorem range60From25151To3037 : Segment 60 25151 25704 0 3037 :=
  paid (pc:=75) (v:=229952155014) (by decide) source104_valid tests60_104_0 fee60_104_25704 (by decide +kernel)

private theorem tests60_106_3037 : ∀ z∈source106.plan.table,z.1.Valid 60 3037 := by decide +kernel
private theorem fee60_106_25704 :
    PopulationFees20258.bill (n:=25704) (PopulationFees20258.tabulate (25704-1) 256) source106.plan.table+
      4*25704*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*384715221676 := by decide +kernel
private theorem range60From25151To3481 : Segment 60 25151 25704 3037 3481 :=
  paid (pc:=72) (v:=384715221676) (by decide) source106_valid tests60_106_3037 fee60_106_25704 (by decide +kernel)

private theorem tests60_105_3481 : ∀ z∈source105.plan.table,z.1.Valid 60 3481 := by decide +kernel
private theorem fee60_105_25704 :
    PopulationFees20258.bill (n:=25704) (PopulationFees20258.tabulate (25704-1) 256) source105.plan.table+
      4*25704*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*377230655014 := by decide +kernel
private theorem range60From25151To3539 : Segment 60 25151 25704 3481 3539 :=
  paid (pc:=72) (v:=377230655014) (by decide) source105_valid tests60_105_3481 fee60_105_25704 (by decide +kernel)

private theorem tests60_105_3539 : ∀ z∈source105.plan.table,z.1.Valid 60 3539 := by decide +kernel
private theorem range60From25151To3541 : Segment 60 25151 25704 3539 3541 :=
  paid (pc:=72) (v:=377230655014) (by decide) source105_valid tests60_105_3539 fee60_105_25704 (by decide +kernel)

private theorem range60From25151 : Win 60 25151 25704 :=
  complete (by decide) (by decide) (join_population (join_population range60From25151To3037 range60From25151To3481) (join_population range60From25151To3539 range60From25151To3541))

private theorem fee60_104_26267 :
    PopulationFees20258.bill (n:=26267) (PopulationFees20258.tabulate (26267-1) 256) source104.plan.table+
      4*26267*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*239335216671 := by decide +kernel
private theorem range60From25705To3071 : Segment 60 25705 26267 0 3071 :=
  paid (pc:=76) (v:=239335216671) (by decide) source104_valid tests60_104_0 fee60_104_26267 (by decide +kernel)

private theorem tests60_105_3071 : ∀ z∈source105.plan.table,z.1.Valid 60 3071 := by decide +kernel
private theorem fee60_105_26267 :
    PopulationFees20258.bill (n:=26267) (PopulationFees20258.tabulate (26267-1) 256) source105.plan.table+
      4*26267*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*392410138356 := by decide +kernel
private theorem range60From25705To3528 : Segment 60 25705 26267 3071 3528 :=
  paid (pc:=72) (v:=392410138356) (by decide) source105_valid tests60_105_3071 fee60_105_26267 (by decide +kernel)

private theorem tests60_105_3528 : ∀ z∈source105.plan.table,z.1.Valid 60 3528 := by decide +kernel
private theorem range60From25705To3541 : Segment 60 25705 26267 3528 3541 :=
  paid (pc:=72) (v:=392410138356) (by decide) source105_valid tests60_105_3528 fee60_105_26267 (by decide +kernel)

private theorem range60From25705 : Win 60 25705 26267 :=
  complete (by decide) (by decide) (join_population range60From25705To3071 (join_population range60From25705To3528 range60From25705To3541))

private theorem fee60_104_26852 :
    PopulationFees20258.bill (n:=26852) (PopulationFees20258.tabulate (26852-1) 256) source104.plan.table+
      4*26852*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*249322383832 := by decide +kernel
private theorem range60From26268To3104 : Segment 60 26268 26852 0 3104 :=
  paid (pc:=76) (v:=249322383832) (by decide) source104_valid tests60_104_0 fee60_104_26852 (by decide +kernel)

private theorem tests60_105_3104 : ∀ z∈source105.plan.table,z.1.Valid 60 3104 := by decide +kernel
private theorem fee60_105_26852 :
    PopulationFees20258.bill (n:=26852) (PopulationFees20258.tabulate (26852-1) 256) source105.plan.table+
      4*26852*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*408528501053 := by decide +kernel
private theorem range60From26268To3529 : Segment 60 26268 26852 3104 3529 :=
  paid (pc:=73) (v:=408528501053) (by decide) source105_valid tests60_105_3104 fee60_105_26852 (by decide +kernel)

private theorem tests60_105_3529 : ∀ z∈source105.plan.table,z.1.Valid 60 3529 := by decide +kernel
private theorem range60From26268To3541 : Segment 60 26268 26852 3529 3541 :=
  paid (pc:=73) (v:=408528501053) (by decide) source105_valid tests60_105_3529 fee60_105_26852 (by decide +kernel)

private theorem range60From26268 : Win 60 26268 26852 :=
  complete (by decide) (by decide) (join_population range60From26268To3104 (join_population range60From26268To3529 range60From26268To3541))

private theorem fee60_104_27472 :
    PopulationFees20258.bill (n:=27472) (PopulationFees20258.tabulate (27472-1) 256) source104.plan.table+
      4*27472*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*260100747860 := by decide +kernel
private theorem range60From26853To3135 : Segment 60 26853 27472 0 3135 :=
  paid (pc:=76) (v:=260100747860) (by decide) source104_valid tests60_104_0 fee60_104_27472 (by decide +kernel)

private theorem tests60_105_3135 : ∀ z∈source105.plan.table,z.1.Valid 60 3135 := by decide +kernel
private theorem fee60_105_27472 :
    PopulationFees20258.bill (n:=27472) (PopulationFees20258.tabulate (27472-1) 256) source105.plan.table+
      4*27472*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*425936144335 := by decide +kernel
private theorem range60From26853To3531 : Segment 60 26853 27472 3135 3531 :=
  paid (pc:=73) (v:=425936144335) (by decide) source105_valid tests60_105_3135 fee60_105_27472 (by decide +kernel)

private theorem tests60_105_3531 : ∀ z∈source105.plan.table,z.1.Valid 60 3531 := by decide +kernel
private theorem range60From26853To3541 : Segment 60 26853 27472 3531 3541 :=
  paid (pc:=73) (v:=425936144335) (by decide) source105_valid tests60_105_3531 fee60_105_27472 (by decide +kernel)

private theorem range60From26853 : Win 60 26853 27472 :=
  complete (by decide) (by decide) (join_population range60From26853To3135 (join_population range60From26853To3531 range60From26853To3541))

private theorem fee60_104_28140 :
    PopulationFees20258.bill (n:=28140) (PopulationFees20258.tabulate (28140-1) 256) source104.plan.table+
      4*28140*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*272088583947 := by decide +kernel
private theorem range60From27473To3164 : Segment 60 27473 28140 0 3164 :=
  paid (pc:=76) (v:=272088583947) (by decide) source104_valid tests60_104_0 fee60_104_28140 (by decide +kernel)

private theorem tests60_105_3164 : ∀ z∈source105.plan.table,z.1.Valid 60 3164 := by decide +kernel
private theorem fee60_105_28140 :
    PopulationFees20258.bill (n:=28140) (PopulationFees20258.tabulate (28140-1) 256) source105.plan.table+
      4*28140*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*445264928845 := by decide +kernel
private theorem range60From27473To3532 : Segment 60 27473 28140 3164 3532 :=
  paid (pc:=74) (v:=445264928845) (by decide) source105_valid tests60_105_3164 fee60_105_28140 (by decide +kernel)

private theorem tests60_105_3532 : ∀ z∈source105.plan.table,z.1.Valid 60 3532 := by decide +kernel
private theorem range60From27473To3541 : Segment 60 27473 28140 3532 3541 :=
  paid (pc:=74) (v:=445264928845) (by decide) source105_valid tests60_105_3532 fee60_105_28140 (by decide +kernel)

private theorem range60From27473 : Win 60 27473 28140 :=
  complete (by decide) (by decide) (join_population range60From27473To3164 (join_population range60From27473To3532 range60From27473To3541))

private theorem fee60_104_28878 :
    PopulationFees20258.bill (n:=28878) (PopulationFees20258.tabulate (28878-1) 256) source104.plan.table+
      4*28878*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*285465392919 := by decide +kernel
private theorem range60From28141To3192 : Segment 60 28141 28878 0 3192 :=
  paid (pc:=76) (v:=285465392919) (by decide) source104_valid tests60_104_0 fee60_104_28878 (by decide +kernel)

private theorem tests60_105_3192 : ∀ z∈source105.plan.table,z.1.Valid 60 3192 := by decide +kernel
private theorem fee60_105_28878 :
    PopulationFees20258.bill (n:=28878) (PopulationFees20258.tabulate (28878-1) 256) source105.plan.table+
      4*28878*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*466819550529 := by decide +kernel
private theorem range60From28141To3533 : Segment 60 28141 28878 3192 3533 :=
  paid (pc:=74) (v:=466819550529) (by decide) source105_valid tests60_105_3192 fee60_105_28878 (by decide +kernel)

private theorem range60From28141To3541 : Segment 60 28141 28878 3533 3541 :=
  paid (pc:=74) (v:=466819550529) (by decide) source105_valid tests60_105_3533 fee60_105_28878 (by decide +kernel)

private theorem range60From28141 : Win 60 28141 28878 :=
  complete (by decide) (by decide) (join_population range60From28141To3192 (join_population range60From28141To3533 range60From28141To3541))

theorem cut60From24593 : Win 60 24593 28878 :=
  (join_ground (join_ground range60From24593 (join_ground range60From25151 range60From25705)) (join_ground (join_ground range60From26268 range60From26853) (join_ground range60From27473 range60From28141)))

end JSP233.FiniteCutRanges20258
