module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Arithmetic.N20258.Sources.Source108

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests61_107_0 : ∀ z∈source107.plan.table,z.1.Valid 61 0 := by decide +kernel
private theorem fee61_107_26832 :
    PopulationFees20258.bill (n:=26832) (PopulationFees20258.tabulate (26832-1) 256) source107.plan.table+
      4*26832*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*296255031376 := by decide +kernel
private theorem range61From26041To3132 : Segment 61 26041 26832 0 3132 :=
  paid (pc:=74) (v:=296255031376) (by decide) source107_valid tests61_107_0 fee61_107_26832 (by decide +kernel)

private theorem tests61_105_3132 : ∀ z∈source105.plan.table,z.1.Valid 61 3132 := by decide +kernel
private theorem fee61_105_26832 :
    PopulationFees20258.bill (n:=26832) (PopulationFees20258.tabulate (26832-1) 256) source105.plan.table+
      4*26832*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*408040566690 := by decide +kernel
private theorem range61From26041To3412 : Segment 61 26041 26832 3132 3412 :=
  paid (pc:=73) (v:=408040566690) (by decide) source105_valid tests61_105_3132 fee61_105_26832 (by decide +kernel)

private theorem tests61_105_3412 : ∀ z∈source105.plan.table,z.1.Valid 61 3412 := by decide +kernel
private theorem range61From26041To3419 : Segment 61 26041 26832 3412 3419 :=
  paid (pc:=73) (v:=408040566690) (by decide) source105_valid tests61_105_3412 fee61_105_26832 (by decide +kernel)

private theorem tests61_108_3419 : ∀ z∈source108.plan.table,z.1.Valid 61 3419 := by decide +kernel
private theorem fee61_108_26832 :
    PopulationFees20258.bill (n:=26832) (PopulationFees20258.tabulate (26832-1) 256) source108.plan.table+
      4*26832*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*336721906236 := by decide +kernel
private theorem range61From26041To3661 : Segment 61 26041 26832 3419 3661 :=
  paid (pc:=70) (v:=336721906236) (by decide) source108_valid tests61_108_3419 fee61_108_26832 (by decide +kernel)

private theorem range61From26041 : Win 61 26041 26832 :=
  complete (by decide) (by decide) (join_population (join_population range61From26041To3132 range61From26041To3412) (join_population range61From26041To3419 range61From26041To3661))

private theorem fee61_107_27684 :
    PopulationFees20258.bill (n:=27684) (PopulationFees20258.tabulate (27684-1) 256) source107.plan.table+
      4*27684*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*313889438331 := by decide +kernel
private theorem range61From26833To3162 : Segment 61 26833 27684 0 3162 :=
  paid (pc:=75) (v:=313889438331) (by decide) source107_valid tests61_107_0 fee61_107_27684 (by decide +kernel)

private theorem tests61_105_3162 : ∀ z∈source105.plan.table,z.1.Valid 61 3162 := by decide +kernel
private theorem fee61_105_27684 :
    PopulationFees20258.bill (n:=27684) (PopulationFees20258.tabulate (27684-1) 256) source105.plan.table+
      4*27684*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*432062203162 := by decide +kernel
private theorem range61From26833To3412 : Segment 61 26833 27684 3162 3412 :=
  paid (pc:=73) (v:=432062203162) (by decide) source105_valid tests61_105_3162 fee61_105_27684 (by decide +kernel)

private theorem range61From26833To3419 : Segment 61 26833 27684 3412 3419 :=
  paid (pc:=73) (v:=432062203162) (by decide) source105_valid tests61_105_3412 fee61_105_27684 (by decide +kernel)

private theorem fee61_108_27684 :
    PopulationFees20258.bill (n:=27684) (PopulationFees20258.tabulate (27684-1) 256) source108.plan.table+
      4*27684*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*356782559034 := by decide +kernel
private theorem range61From26833To3661 : Segment 61 26833 27684 3419 3661 :=
  paid (pc:=71) (v:=356782559034) (by decide) source108_valid tests61_108_3419 fee61_108_27684 (by decide +kernel)

private theorem range61From26833 : Win 61 26833 27684 :=
  complete (by decide) (by decide) (join_population (join_population range61From26833To3162 range61From26833To3412) (join_population range61From26833To3419 range61From26833To3661))

private theorem fee61_107_28620 :
    PopulationFees20258.bill (n:=28620) (PopulationFees20258.tabulate (28620-1) 256) source107.plan.table+
      4*28620*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*333836325197 := by decide +kernel
private theorem range61From27685To3192 : Segment 61 27685 28620 0 3192 :=
  paid (pc:=75) (v:=333836325197) (by decide) source107_valid tests61_107_0 fee61_107_28620 (by decide +kernel)

private theorem tests61_105_3192 : ∀ z∈source105.plan.table,z.1.Valid 61 3192 := by decide +kernel
private theorem fee61_105_28620 :
    PopulationFees20258.bill (n:=28620) (PopulationFees20258.tabulate (28620-1) 256) source105.plan.table+
      4*28620*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*459253021018 := by decide +kernel
private theorem range61From27685To3415 : Segment 61 27685 28620 3192 3415 :=
  paid (pc:=74) (v:=459253021018) (by decide) source105_valid tests61_105_3192 fee61_105_28620 (by decide +kernel)

private theorem tests61_105_3415 : ∀ z∈source105.plan.table,z.1.Valid 61 3415 := by decide +kernel
private theorem range61From27685To3420 : Segment 61 27685 28620 3415 3420 :=
  paid (pc:=74) (v:=459253021018) (by decide) source105_valid tests61_105_3415 fee61_105_28620 (by decide +kernel)

private theorem tests61_108_3420 : ∀ z∈source108.plan.table,z.1.Valid 61 3420 := by decide +kernel
private theorem fee61_108_28620 :
    PopulationFees20258.bill (n:=28620) (PopulationFees20258.tabulate (28620-1) 256) source108.plan.table+
      4*28620*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*379502540482 := by decide +kernel
private theorem range61From27685To3661 : Segment 61 27685 28620 3420 3661 :=
  paid (pc:=72) (v:=379502540482) (by decide) source108_valid tests61_108_3420 fee61_108_28620 (by decide +kernel)

private theorem range61From27685 : Win 61 27685 28620 :=
  complete (by decide) (by decide) (join_population (join_population range61From27685To3192 range61From27685To3415) (join_population range61From27685To3420 range61From27685To3661))

private theorem fee61_107_29680 :
    PopulationFees20258.bill (n:=29680) (PopulationFees20258.tabulate (29680-1) 256) source107.plan.table+
      4*29680*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*357045006522 := by decide +kernel
private theorem range61From28621To3218 : Segment 61 28621 29680 0 3218 :=
  paid (pc:=75) (v:=357045006522) (by decide) source107_valid tests61_107_0 fee61_107_29680 (by decide +kernel)

private theorem tests61_105_3218 : ∀ z∈source105.plan.table,z.1.Valid 61 3218 := by decide +kernel
private theorem fee61_105_29680 :
    PopulationFees20258.bill (n:=29680) (PopulationFees20258.tabulate (29680-1) 256) source105.plan.table+
      4*29680*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*490961144512 := by decide +kernel
private theorem range61From28621To3414 : Segment 61 28621 29680 3218 3414 :=
  paid (pc:=74) (v:=490961144512) (by decide) source105_valid tests61_105_3218 fee61_105_29680 (by decide +kernel)

private theorem tests61_105_3414 : ∀ z∈source105.plan.table,z.1.Valid 61 3414 := by decide +kernel
private theorem range61From28621To3419 : Segment 61 28621 29680 3414 3419 :=
  paid (pc:=74) (v:=490961144512) (by decide) source105_valid tests61_105_3414 fee61_105_29680 (by decide +kernel)

private theorem fee61_108_29680 :
    PopulationFees20258.bill (n:=29680) (PopulationFees20258.tabulate (29680-1) 256) source108.plan.table+
      4*29680*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*405904125435 := by decide +kernel
private theorem range61From28621To3661 : Segment 61 28621 29680 3419 3661 :=
  paid (pc:=72) (v:=405904125435) (by decide) source108_valid tests61_108_3419 fee61_108_29680 (by decide +kernel)

private theorem range61From28621 : Win 61 28621 29680 :=
  complete (by decide) (by decide) (join_population (join_population range61From28621To3218 range61From28621To3414) (join_population range61From28621To3419 range61From28621To3661))

private theorem fee61_107_30904 :
    PopulationFees20258.bill (n:=30904) (PopulationFees20258.tabulate (30904-1) 256) source107.plan.table+
      4*30904*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*384888300271 := by decide +kernel
private theorem range61From29681To3246 : Segment 61 29681 30904 0 3246 :=
  paid (pc:=75) (v:=384888300271) (by decide) source107_valid tests61_107_0 fee61_107_30904 (by decide +kernel)

private theorem tests61_105_3246 : ∀ z∈source105.plan.table,z.1.Valid 61 3246 := by decide +kernel
private theorem fee61_105_30904 :
    PopulationFees20258.bill (n:=30904) (PopulationFees20258.tabulate (30904-1) 256) source105.plan.table+
      4*30904*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*528893643823 := by decide +kernel
private theorem range61From29681To3416 : Segment 61 29681 30904 3246 3416 :=
  paid (pc:=74) (v:=528893643823) (by decide) source105_valid tests61_105_3246 fee61_105_30904 (by decide +kernel)

private theorem tests61_105_3416 : ∀ z∈source105.plan.table,z.1.Valid 61 3416 := by decide +kernel
private theorem range61From29681To3419 : Segment 61 29681 30904 3416 3419 :=
  paid (pc:=74) (v:=528893643823) (by decide) source105_valid tests61_105_3416 fee61_105_30904 (by decide +kernel)

private theorem fee61_108_30904 :
    PopulationFees20258.bill (n:=30904) (PopulationFees20258.tabulate (30904-1) 256) source108.plan.table+
      4*30904*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*437621060582 := by decide +kernel
private theorem range61From29681To3661 : Segment 61 29681 30904 3419 3661 :=
  paid (pc:=73) (v:=437621060582) (by decide) source108_valid tests61_108_3419 fee61_108_30904 (by decide +kernel)

private theorem range61From29681 : Win 61 29681 30904 :=
  complete (by decide) (by decide) (join_population (join_population range61From29681To3246 range61From29681To3416) (join_population range61From29681To3419 range61From29681To3661))

private theorem fee61_107_32348 :
    PopulationFees20258.bill (n:=32348) (PopulationFees20258.tabulate (32348-1) 256) source107.plan.table+
      4*32348*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*419084887760 := by decide +kernel
private theorem range61From30905To3274 : Segment 61 30905 32348 0 3274 :=
  paid (pc:=75) (v:=419084887760) (by decide) source107_valid tests61_107_0 fee61_107_32348 (by decide +kernel)

private theorem tests61_105_3274 : ∀ z∈source105.plan.table,z.1.Valid 61 3274 := by decide +kernel
private theorem fee61_105_32348 :
    PopulationFees20258.bill (n:=32348) (PopulationFees20258.tabulate (32348-1) 256) source105.plan.table+
      4*32348*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*575716864099 := by decide +kernel
private theorem range61From30905To3416 : Segment 61 30905 32348 3274 3416 :=
  paid (pc:=74) (v:=575716864099) (by decide) source105_valid tests61_105_3274 fee61_105_32348 (by decide +kernel)

private theorem range61From30905To3419 : Segment 61 30905 32348 3416 3419 :=
  paid (pc:=74) (v:=575716864099) (by decide) source105_valid tests61_105_3416 fee61_105_32348 (by decide +kernel)

private theorem fee61_108_32348 :
    PopulationFees20258.bill (n:=32348) (PopulationFees20258.tabulate (32348-1) 256) source108.plan.table+
      4*32348*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*476561227862 := by decide +kernel
private theorem range61From30905To3661 : Segment 61 30905 32348 3419 3661 :=
  paid (pc:=73) (v:=476561227862) (by decide) source108_valid tests61_108_3419 fee61_108_32348 (by decide +kernel)

private theorem range61From30905 : Win 61 30905 32348 :=
  complete (by decide) (by decide) (join_population (join_population range61From30905To3274 range61From30905To3416) (join_population range61From30905To3419 range61From30905To3661))

theorem cut61From26041 : Win 61 26041 32348 :=
  (join_ground (join_ground range61From26041 (join_ground range61From26833 range61From27685)) (join_ground range61From28621 (join_ground range61From29681 range61From30905)))

end JSP233.FiniteCutRanges20258
