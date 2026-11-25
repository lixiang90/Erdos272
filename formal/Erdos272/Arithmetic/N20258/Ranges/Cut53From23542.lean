module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source046
public import Erdos272.Arithmetic.N20258.Sources.Source052
public import Erdos272.Arithmetic.N20258.Sources.Source054
public import Erdos272.Arithmetic.N20258.Sources.Source057
public import Erdos272.Arithmetic.N20258.Sources.Source060
public import Erdos272.Arithmetic.N20258.Sources.Source062
public import Erdos272.Arithmetic.N20258.Sources.Source064
public import Erdos272.Arithmetic.N20258.Sources.Source068
public import Erdos272.Arithmetic.N20258.Sources.Source069
public import Erdos272.Arithmetic.N20258.Sources.Source070
public import Erdos272.Arithmetic.N20258.Sources.Source072
public import Erdos272.Arithmetic.N20258.Sources.Source073

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests53_057_0 : ∀ z∈source057.plan.table,z.1.Valid 53 0 := by decide +kernel
private theorem fee53_057_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source057.plan.table+
      4*24200*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*200367030417 := by decide +kernel
private theorem range53From23542To2424 : Segment 53 23542 24200 0 2424 :=
  paid (pc:=78) (v:=200367030417) (by decide) source057_valid tests53_057_0 fee53_057_24200 (by decide +kernel)

private theorem tests53_060_2424 : ∀ z∈source060.plan.table,z.1.Valid 53 2424 := by decide +kernel
private theorem fee53_060_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source060.plan.table+
      4*24200*NaturalPopulation20258.weights source060.extras≤source060.plan.scale*230638379668 := by decide +kernel
private theorem range53From23542To2536 : Segment 53 23542 24200 2424 2536 :=
  paid (pc:=77) (v:=230638379668) (by decide) source060_valid tests53_060_2424 fee53_060_24200 (by decide +kernel)

private theorem tests53_068_2536 : ∀ z∈source068.plan.table,z.1.Valid 53 2536 := by decide +kernel
private theorem fee53_068_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source068.plan.table+
      4*24200*NaturalPopulation20258.weights source068.extras≤source068.plan.scale*275806098848 := by decide +kernel
private theorem range53From23542To2603 : Segment 53 23542 24200 2536 2603 :=
  paid (pc:=77) (v:=275806098848) (by decide) source068_valid tests53_068_2536 fee53_068_24200 (by decide +kernel)

private theorem tests53_072_2603 : ∀ z∈source072.plan.table,z.1.Valid 53 2603 := by decide +kernel
private theorem fee53_072_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source072.plan.table+
      4*24200*NaturalPopulation20258.weights source072.extras≤source072.plan.scale*329746342038 := by decide +kernel
private theorem range53From23542To2644 : Segment 53 23542 24200 2603 2644 :=
  paid (pc:=76) (v:=329746342038) (by decide) source072_valid tests53_072_2603 fee53_072_24200 (by decide +kernel)

private theorem tests53_073_2644 : ∀ z∈source073.plan.table,z.1.Valid 53 2644 := by decide +kernel
private theorem fee53_073_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source073.plan.table+
      4*24200*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*379275292714 := by decide +kernel
private theorem range53From23542To2718 : Segment 53 23542 24200 2644 2718 :=
  paid (pc:=76) (v:=379275292714) (by decide) source073_valid tests53_073_2644 fee53_073_24200 (by decide +kernel)

private theorem tests53_069_2718 : ∀ z∈source069.plan.table,z.1.Valid 53 2718 := by decide +kernel
private theorem fee53_069_24200 :
    PopulationFees20258.bill (n:=24200) (PopulationFees20258.tabulate (24200-1) 256) source069.plan.table+
      4*24200*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*242036651051 := by decide +kernel
private theorem range53From23542To2757 : Segment 53 23542 24200 2718 2757 :=
  paid (pc:=75) (v:=242036651051) (by decide) source069_valid tests53_069_2718 fee53_069_24200 (by decide +kernel)

private theorem range53From23542 : Win 53 23542 24200 :=
  complete (by decide) (by decide) (join_population (join_population range53From23542To2424 (join_population range53From23542To2536 range53From23542To2603)) (join_population range53From23542To2644 (join_population range53From23542To2718 range53From23542To2757)))

private theorem fee53_057_24981 :
    PopulationFees20258.bill (n:=24981) (PopulationFees20258.tabulate (24981-1) 256) source057.plan.table+
      4*24981*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*212453390096 := by decide +kernel
private theorem range53From24201To2444 : Segment 53 24201 24981 0 2444 :=
  paid (pc:=78) (v:=212453390096) (by decide) source057_valid tests53_057_0 fee53_057_24981 (by decide +kernel)

private theorem tests53_060_2444 : ∀ z∈source060.plan.table,z.1.Valid 53 2444 := by decide +kernel
private theorem fee53_060_24981 :
    PopulationFees20258.bill (n:=24981) (PopulationFees20258.tabulate (24981-1) 256) source060.plan.table+
      4*24981*NaturalPopulation20258.weights source060.extras≤source060.plan.scale*244519126556 := by decide +kernel
private theorem range53From24201To2549 : Segment 53 24201 24981 2444 2549 :=
  paid (pc:=77) (v:=244519126556) (by decide) source060_valid tests53_060_2444 fee53_060_24981 (by decide +kernel)

private theorem tests53_054_2549 : ∀ z∈source054.plan.table,z.1.Valid 53 2549 := by decide +kernel
private theorem fee53_054_24981 :
    PopulationFees20258.bill (n:=24981) (PopulationFees20258.tabulate (24981-1) 256) source054.plan.table+
      4*24981*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*291349065495 := by decide +kernel
private theorem range53From24201To2614 : Segment 53 24201 24981 2549 2614 :=
  paid (pc:=76) (v:=291349065495) (by decide) source054_valid tests53_054_2549 fee53_054_24981 (by decide +kernel)

private theorem tests53_070_2614 : ∀ z∈source070.plan.table,z.1.Valid 53 2614 := by decide +kernel
private theorem fee53_070_24981 :
    PopulationFees20258.bill (n:=24981) (PopulationFees20258.tabulate (24981-1) 256) source070.plan.table+
      4*24981*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*271578717167 := by decide +kernel
private theorem range53From24201To2695 : Segment 53 24201 24981 2614 2695 :=
  paid (pc:=76) (v:=271578717167) (by decide) source070_valid tests53_070_2614 fee53_070_24981 (by decide +kernel)

private theorem tests53_069_2695 : ∀ z∈source069.plan.table,z.1.Valid 53 2695 := by decide +kernel
private theorem fee53_069_24981 :
    PopulationFees20258.bill (n:=24981) (PopulationFees20258.tabulate (24981-1) 256) source069.plan.table+
      4*24981*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*256758220589 := by decide +kernel
private theorem range53From24201To2755 : Segment 53 24201 24981 2695 2755 :=
  paid (pc:=75) (v:=256758220589) (by decide) source069_valid tests53_069_2695 fee53_069_24981 (by decide +kernel)

private theorem tests53_069_2755 : ∀ z∈source069.plan.table,z.1.Valid 53 2755 := by decide +kernel
private theorem range53From24201To2757 : Segment 53 24201 24981 2755 2757 :=
  paid (pc:=75) (v:=256758220589) (by decide) source069_valid tests53_069_2755 fee53_069_24981 (by decide +kernel)

private theorem range53From24201 : Win 53 24201 24981 :=
  complete (by decide) (by decide) (join_population (join_population range53From24201To2444 (join_population range53From24201To2549 range53From24201To2614)) (join_population range53From24201To2695 (join_population range53From24201To2755 range53From24201To2757)))

private theorem fee53_057_25920 :
    PopulationFees20258.bill (n:=25920) (PopulationFees20258.tabulate (25920-1) 256) source057.plan.table+
      4*25920*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*227520004483 := by decide +kernel
private theorem range53From24982To2469 : Segment 53 24982 25920 0 2469 :=
  paid (pc:=77) (v:=227520004483) (by decide) source057_valid tests53_057_0 fee53_057_25920 (by decide +kernel)

private theorem tests53_052_2469 : ∀ z∈source052.plan.table,z.1.Valid 53 2469 := by decide +kernel
private theorem fee53_052_25920 :
    PopulationFees20258.bill (n:=25920) (PopulationFees20258.tabulate (25920-1) 256) source052.plan.table+
      4*25920*NaturalPopulation20258.weights source052.extras≤source052.plan.scale*259344776943 := by decide +kernel
private theorem range53From24982To2574 : Segment 53 24982 25920 2469 2574 :=
  paid (pc:=77) (v:=259344776943) (by decide) source052_valid tests53_052_2469 fee53_052_25920 (by decide +kernel)

private theorem tests53_072_2574 : ∀ z∈source072.plan.table,z.1.Valid 53 2574 := by decide +kernel
private theorem fee53_072_25920 :
    PopulationFees20258.bill (n:=25920) (PopulationFees20258.tabulate (25920-1) 256) source072.plan.table+
      4*25920*NaturalPopulation20258.weights source072.extras≤source072.plan.scale*374200170270 := by decide +kernel
private theorem range53From24982To2638 : Segment 53 24982 25920 2574 2638 :=
  paid (pc:=76) (v:=374200170270) (by decide) source072_valid tests53_072_2574 fee53_072_25920 (by decide +kernel)

private theorem tests53_070_2638 : ∀ z∈source070.plan.table,z.1.Valid 53 2638 := by decide +kernel
private theorem fee53_070_25920 :
    PopulationFees20258.bill (n:=25920) (PopulationFees20258.tabulate (25920-1) 256) source070.plan.table+
      4*25920*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*290937617158 := by decide +kernel
private theorem range53From24982To2698 : Segment 53 24982 25920 2638 2698 :=
  paid (pc:=76) (v:=290937617158) (by decide) source070_valid tests53_070_2638 fee53_070_25920 (by decide +kernel)

private theorem tests53_069_2698 : ∀ z∈source069.plan.table,z.1.Valid 53 2698 := by decide +kernel
private theorem fee53_069_25920 :
    PopulationFees20258.bill (n:=25920) (PopulationFees20258.tabulate (25920-1) 256) source069.plan.table+
      4*25920*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*275104374988 := by decide +kernel
private theorem range53From24982To2756 : Segment 53 24982 25920 2698 2756 :=
  paid (pc:=76) (v:=275104374988) (by decide) source069_valid tests53_069_2698 fee53_069_25920 (by decide +kernel)

private theorem tests53_069_2756 : ∀ z∈source069.plan.table,z.1.Valid 53 2756 := by decide +kernel
private theorem range53From24982To2757 : Segment 53 24982 25920 2756 2757 :=
  paid (pc:=76) (v:=275104374988) (by decide) source069_valid tests53_069_2756 fee53_069_25920 (by decide +kernel)

private theorem range53From24982 : Win 53 24982 25920 :=
  complete (by decide) (by decide) (join_population (join_population range53From24982To2469 (join_population range53From24982To2574 range53From24982To2638)) (join_population range53From24982To2698 (join_population range53From24982To2756 range53From24982To2757)))

private theorem fee53_057_27072 :
    PopulationFees20258.bill (n:=27072) (PopulationFees20258.tabulate (27072-1) 256) source057.plan.table+
      4*27072*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*246626961641 := by decide +kernel
private theorem range53From25921To2492 : Segment 53 25921 27072 0 2492 :=
  paid (pc:=77) (v:=246626961641) (by decide) source057_valid tests53_057_0 fee53_057_27072 (by decide +kernel)

private theorem tests53_064_2492 : ∀ z∈source064.plan.table,z.1.Valid 53 2492 := by decide +kernel
private theorem fee53_064_27072 :
    PopulationFees20258.bill (n:=27072) (PopulationFees20258.tabulate (27072-1) 256) source064.plan.table+
      4*27072*NaturalPopulation20258.weights source064.extras≤source064.plan.scale*343202673725 := by decide +kernel
private theorem range53From25921To2608 : Segment 53 25921 27072 2492 2608 :=
  paid (pc:=76) (v:=343202673725) (by decide) source064_valid tests53_064_2492 fee53_064_27072 (by decide +kernel)

private theorem tests53_046_2608 : ∀ z∈source046.plan.table,z.1.Valid 53 2608 := by decide +kernel
private theorem fee53_046_27072 :
    PopulationFees20258.bill (n:=27072) (PopulationFees20258.tabulate (27072-1) 256) source046.plan.table+
      4*27072*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*332971028069 := by decide +kernel
private theorem range53From25921To2644 : Segment 53 25921 27072 2608 2644 :=
  paid (pc:=76) (v:=332971028069) (by decide) source046_valid tests53_046_2608 fee53_046_27072 (by decide +kernel)

private theorem tests53_062_2644 : ∀ z∈source062.plan.table,z.1.Valid 53 2644 := by decide +kernel
private theorem fee53_062_27072 :
    PopulationFees20258.bill (n:=27072) (PopulationFees20258.tabulate (27072-1) 256) source062.plan.table+
      4*27072*NaturalPopulation20258.weights source062.extras≤source062.plan.scale*313553872773 := by decide +kernel
private theorem range53From25921To2706 : Segment 53 25921 27072 2644 2706 :=
  paid (pc:=76) (v:=313553872773) (by decide) source062_valid tests53_062_2644 fee53_062_27072 (by decide +kernel)

private theorem tests53_069_2706 : ∀ z∈source069.plan.table,z.1.Valid 53 2706 := by decide +kernel
private theorem fee53_069_27072 :
    PopulationFees20258.bill (n:=27072) (PopulationFees20258.tabulate (27072-1) 256) source069.plan.table+
      4*27072*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*298413756568 := by decide +kernel
private theorem range53From25921To2757 : Segment 53 25921 27072 2706 2757 :=
  paid (pc:=75) (v:=298413756568) (by decide) source069_valid tests53_069_2706 fee53_069_27072 (by decide +kernel)

private theorem range53From25921 : Win 53 25921 27072 :=
  complete (by decide) (by decide) (join_population (join_population range53From25921To2492 range53From25921To2608) (join_population range53From25921To2644 (join_population range53From25921To2706 range53From25921To2757)))

theorem cut53From23542 : Win 53 23542 27072 :=
  (join_ground (join_ground range53From23542 range53From24201) (join_ground range53From24982 range53From25921))

end JSP233.FiniteCutRanges20258
