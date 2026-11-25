module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source104
public import Erdos272.Arithmetic.N20258.Sources.Source105

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests60_104_0 : ∀ z∈source104.plan.table,z.1.Valid 60 0 := by decide +kernel
private theorem fee60_104_29700 :
    PopulationFees20258.bill (n:=29700) (PopulationFees20258.tabulate (29700-1) 256) source104.plan.table+
      4*29700*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*300998267143 := by decide +kernel
private theorem range60From28879To3223 : Segment 60 28879 29700 0 3223 :=
  paid (pc:=76) (v:=300998267143) (by decide) source104_valid tests60_104_0 fee60_104_29700 (by decide +kernel)

private theorem tests60_105_3223 : ∀ z∈source105.plan.table,z.1.Valid 60 3223 := by decide +kernel
private theorem fee60_105_29700 :
    PopulationFees20258.bill (n:=29700) (PopulationFees20258.tabulate (29700-1) 256) source105.plan.table+
      4*29700*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*491807184114 := by decide +kernel
private theorem range60From28879To3535 : Segment 60 28879 29700 3223 3535 :=
  paid (pc:=74) (v:=491807184114) (by decide) source105_valid tests60_105_3223 fee60_105_29700 (by decide +kernel)

private theorem tests60_105_3535 : ∀ z∈source105.plan.table,z.1.Valid 60 3535 := by decide +kernel
private theorem range60From28879To3541 : Segment 60 28879 29700 3535 3541 :=
  paid (pc:=74) (v:=491807184114) (by decide) source105_valid tests60_105_3535 fee60_105_29700 (by decide +kernel)

private theorem range60From28879 : Win 60 28879 29700 :=
  complete (by decide) (by decide) (join_population range60From28879To3223 (join_population range60From28879To3535 range60From28879To3541))

private theorem fee60_104_30641 :
    PopulationFees20258.bill (n:=30641) (PopulationFees20258.tabulate (30641-1) 256) source104.plan.table+
      4*30641*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*319001388330 := by decide +kernel
private theorem range60From29701To3251 : Segment 60 29701 30641 0 3251 :=
  paid (pc:=76) (v:=319001388330) (by decide) source104_valid tests60_104_0 fee60_104_30641 (by decide +kernel)

private theorem tests60_105_3251 : ∀ z∈source105.plan.table,z.1.Valid 60 3251 := by decide +kernel
private theorem fee60_105_30641 :
    PopulationFees20258.bill (n:=30641) (PopulationFees20258.tabulate (30641-1) 256) source105.plan.table+
      4*30641*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*520862444359 := by decide +kernel
private theorem range60From29701To3535 : Segment 60 29701 30641 3251 3535 :=
  paid (pc:=75) (v:=520862444359) (by decide) source105_valid tests60_105_3251 fee60_105_30641 (by decide +kernel)

private theorem range60From29701To3541 : Segment 60 29701 30641 3535 3541 :=
  paid (pc:=75) (v:=520862444359) (by decide) source105_valid tests60_105_3535 fee60_105_30641 (by decide +kernel)

private theorem range60From29701 : Win 60 29701 30641 :=
  complete (by decide) (by decide) (join_population range60From29701To3251 (join_population range60From29701To3535 range60From29701To3541))

private theorem fee60_104_31740 :
    PopulationFees20258.bill (n:=31740) (PopulationFees20258.tabulate (31740-1) 256) source104.plan.table+
      4*31740*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*340655359692 := by decide +kernel
private theorem range60From30642To3280 : Segment 60 30642 31740 0 3280 :=
  paid (pc:=76) (v:=340655359692) (by decide) source104_valid tests60_104_0 fee60_104_31740 (by decide +kernel)

private theorem tests60_105_3280 : ∀ z∈source105.plan.table,z.1.Valid 60 3280 := by decide +kernel
private theorem fee60_105_31740 :
    PopulationFees20258.bill (n:=31740) (PopulationFees20258.tabulate (31740-1) 256) source105.plan.table+
      4*31740*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*555723908110 := by decide +kernel
private theorem range60From30642To3535 : Segment 60 30642 31740 3280 3535 :=
  paid (pc:=75) (v:=555723908110) (by decide) source105_valid tests60_105_3280 fee60_105_31740 (by decide +kernel)

private theorem range60From30642To3541 : Segment 60 30642 31740 3535 3541 :=
  paid (pc:=75) (v:=555723908110) (by decide) source105_valid tests60_105_3535 fee60_105_31740 (by decide +kernel)

private theorem range60From30642 : Win 60 30642 31740 :=
  complete (by decide) (by decide) (join_population range60From30642To3280 (join_population range60From30642To3535 range60From30642To3541))

private theorem fee60_104_33042 :
    PopulationFees20258.bill (n:=33042) (PopulationFees20258.tabulate (33042-1) 256) source104.plan.table+
      4*33042*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*367452605815 := by decide +kernel
private theorem range60From31741To3312 : Segment 60 31741 33042 0 3312 :=
  paid (pc:=76) (v:=367452605815) (by decide) source104_valid tests60_104_0 fee60_104_33042 (by decide +kernel)

private theorem tests60_105_3312 : ∀ z∈source105.plan.table,z.1.Valid 60 3312 := by decide +kernel
private theorem fee60_105_33042 :
    PopulationFees20258.bill (n:=33042) (PopulationFees20258.tabulate (33042-1) 256) source105.plan.table+
      4*33042*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*598859956441 := by decide +kernel
private theorem range60From31741To3537 : Segment 60 31741 33042 3312 3537 :=
  paid (pc:=75) (v:=598859956441) (by decide) source105_valid tests60_105_3312 fee60_105_33042 (by decide +kernel)

private theorem tests60_105_3537 : ∀ z∈source105.plan.table,z.1.Valid 60 3537 := by decide +kernel
private theorem range60From31741To3541 : Segment 60 31741 33042 3537 3541 :=
  paid (pc:=75) (v:=598859956441) (by decide) source105_valid tests60_105_3537 fee60_105_33042 (by decide +kernel)

private theorem range60From31741 : Win 60 31741 33042 :=
  complete (by decide) (by decide) (join_population range60From31741To3312 (join_population range60From31741To3537 range60From31741To3541))

private theorem fee60_104_34620 :
    PopulationFees20258.bill (n:=34620) (PopulationFees20258.tabulate (34620-1) 256) source104.plan.table+
      4*34620*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*401220188276 := by decide +kernel
private theorem range60From33043To3345 : Segment 60 33043 34620 0 3345 :=
  paid (pc:=76) (v:=401220188276) (by decide) source104_valid tests60_104_0 fee60_104_34620 (by decide +kernel)

private theorem tests60_105_3345 : ∀ z∈source105.plan.table,z.1.Valid 60 3345 := by decide +kernel
private theorem fee60_105_34620 :
    PopulationFees20258.bill (n:=34620) (PopulationFees20258.tabulate (34620-1) 256) source105.plan.table+
      4*34620*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*653156196932 := by decide +kernel
private theorem range60From33043To3537 : Segment 60 33043 34620 3345 3537 :=
  paid (pc:=75) (v:=653156196932) (by decide) source105_valid tests60_105_3345 fee60_105_34620 (by decide +kernel)

private theorem range60From33043To3541 : Segment 60 33043 34620 3537 3541 :=
  paid (pc:=75) (v:=653156196932) (by decide) source105_valid tests60_105_3537 fee60_105_34620 (by decide +kernel)

private theorem range60From33043 : Win 60 33043 34620 :=
  complete (by decide) (by decide) (join_population range60From33043To3345 (join_population range60From33043To3537 range60From33043To3541))

private theorem fee60_104_36572 :
    PopulationFees20258.bill (n:=36572) (PopulationFees20258.tabulate (36572-1) 256) source104.plan.table+
      4*36572*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*445014857983 := by decide +kernel
private theorem range60From34621To3380 : Segment 60 34621 36572 0 3380 :=
  paid (pc:=76) (v:=445014857983) (by decide) source104_valid tests60_104_0 fee60_104_36572 (by decide +kernel)

private theorem tests60_105_3380 : ∀ z∈source105.plan.table,z.1.Valid 60 3380 := by decide +kernel
private theorem fee60_105_36572 :
    PopulationFees20258.bill (n:=36572) (PopulationFees20258.tabulate (36572-1) 256) source105.plan.table+
      4*36572*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*723531572034 := by decide +kernel
private theorem range60From34621To3538 : Segment 60 34621 36572 3380 3538 :=
  paid (pc:=75) (v:=723531572034) (by decide) source105_valid tests60_105_3380 fee60_105_36572 (by decide +kernel)

private theorem tests60_105_3538 : ∀ z∈source105.plan.table,z.1.Valid 60 3538 := by decide +kernel
private theorem range60From34621To3541 : Segment 60 34621 36572 3538 3541 :=
  paid (pc:=75) (v:=723531572034) (by decide) source105_valid tests60_105_3538 fee60_105_36572 (by decide +kernel)

private theorem range60From34621 : Win 60 34621 36572 :=
  complete (by decide) (by decide) (join_population range60From34621To3380 (join_population range60From34621To3538 range60From34621To3541))

private theorem fee60_104_39044 :
    PopulationFees20258.bill (n:=39044) (PopulationFees20258.tabulate (39044-1) 256) source104.plan.table+
      4*39044*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*503621013979 := by decide +kernel
private theorem range60From36573To3417 : Segment 60 36573 39044 0 3417 :=
  paid (pc:=75) (v:=503621013979) (by decide) source104_valid tests60_104_0 fee60_104_39044 (by decide +kernel)

private theorem tests60_105_3417 : ∀ z∈source105.plan.table,z.1.Valid 60 3417 := by decide +kernel
private theorem fee60_105_39044 :
    PopulationFees20258.bill (n:=39044) (PopulationFees20258.tabulate (39044-1) 256) source105.plan.table+
      4*39044*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*817671586938 := by decide +kernel
private theorem range60From36573To3538 : Segment 60 36573 39044 3417 3538 :=
  paid (pc:=75) (v:=817671586938) (by decide) source105_valid tests60_105_3417 fee60_105_39044 (by decide +kernel)

private theorem range60From36573To3541 : Segment 60 36573 39044 3538 3541 :=
  paid (pc:=75) (v:=817671586938) (by decide) source105_valid tests60_105_3538 fee60_105_39044 (by decide +kernel)

private theorem range60From36573 : Win 60 36573 39044 :=
  complete (by decide) (by decide) (join_population range60From36573To3417 (join_population range60From36573To3538 range60From36573To3541))

private theorem range60From39045Price : ( .marked ⟨60,152,23,7000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range60From39045 : Win 60 39045 39999 :=
  classical_route (pc:=80) range60From39045Price (by decide +kernel)

theorem cut60From28879 : Win 60 28879 39999 :=
  (join_ground (join_ground (join_ground range60From28879 range60From29701) (join_ground range60From30642 range60From31741)) (join_ground (join_ground range60From33043 range60From34621) (join_ground range60From36573 range60From39045)))

end JSP233.FiniteCutRanges20258
