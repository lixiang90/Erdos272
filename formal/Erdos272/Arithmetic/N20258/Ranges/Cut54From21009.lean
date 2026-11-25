module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source070
public import Erdos272.Arithmetic.N20258.Sources.Source073
public import Erdos272.Arithmetic.N20258.Sources.Source074
public import Erdos272.Arithmetic.N20258.Sources.Source075
public import Erdos272.Arithmetic.N20258.Sources.Source076
public import Erdos272.Arithmetic.N20258.Sources.Source077
public import Erdos272.Arithmetic.N20258.Sources.Source079
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source081

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests54_074_0 : ∀ z∈source074.plan.table,z.1.Valid 54 0 := by decide +kernel
private theorem fee54_074_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source074.plan.table+
      4*21308*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*142276637952 := by decide +kernel
private theorem range54From21009To2402 : Segment 54 21009 21308 0 2402 :=
  paid (pc:=77) (v:=142276637952) (by decide) source074_valid tests54_074_0 fee54_074_21308 (by decide +kernel)

private theorem tests54_075_2402 : ∀ z∈source075.plan.table,z.1.Valid 54 2402 := by decide +kernel
private theorem fee54_075_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source075.plan.table+
      4*21308*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*183122523907 := by decide +kernel
private theorem range54From21009To2468 : Segment 54 21009 21308 2402 2468 :=
  paid (pc:=77) (v:=183122523907) (by decide) source075_valid tests54_075_2402 fee54_075_21308 (by decide +kernel)

private theorem tests54_076_2468 : ∀ z∈source076.plan.table,z.1.Valid 54 2468 := by decide +kernel
private theorem fee54_076_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source076.plan.table+
      4*21308*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*227656088509 := by decide +kernel
private theorem range54From21009To2514 : Segment 54 21009 21308 2468 2514 :=
  paid (pc:=76) (v:=227656088509) (by decide) source076_valid tests54_076_2468 fee54_076_21308 (by decide +kernel)

private theorem tests54_077_2514 : ∀ z∈source077.plan.table,z.1.Valid 54 2514 := by decide +kernel
private theorem fee54_077_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source077.plan.table+
      4*21308*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*217870021747 := by decide +kernel
private theorem range54From21009To2579 : Segment 54 21009 21308 2514 2579 :=
  paid (pc:=76) (v:=217870021747) (by decide) source077_valid tests54_077_2514 fee54_077_21308 (by decide +kernel)

private theorem tests54_079_2579 : ∀ z∈source079.plan.table,z.1.Valid 54 2579 := by decide +kernel
private theorem fee54_079_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source079.plan.table+
      4*21308*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*260872995097 := by decide +kernel
private theorem range54From21009To2664 : Segment 54 21009 21308 2579 2664 :=
  paid (pc:=75) (v:=260872995097) (by decide) source079_valid tests54_079_2579 fee54_079_21308 (by decide +kernel)

private theorem tests54_070_2664 : ∀ z∈source070.plan.table,z.1.Valid 54 2664 := by decide +kernel
private theorem fee54_070_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source070.plan.table+
      4*21308*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*202462302432 := by decide +kernel
private theorem range54From21009To2686 : Segment 54 21009 21308 2664 2686 :=
  paid (pc:=75) (v:=202462302432) (by decide) source070_valid tests54_070_2664 fee54_070_21308 (by decide +kernel)

private theorem tests54_073_2686 : ∀ z∈source073.plan.table,z.1.Valid 54 2686 := by decide +kernel
private theorem fee54_073_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source073.plan.table+
      4*21308*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*301133163939 := by decide +kernel
private theorem range54From21009To2816 : Segment 54 21009 21308 2686 2816 :=
  paid (pc:=74) (v:=301133163939) (by decide) source073_valid tests54_073_2686 fee54_073_21308 (by decide +kernel)

private theorem tests54_080_2816 : ∀ z∈source080.plan.table,z.1.Valid 54 2816 := by decide +kernel
private theorem fee54_080_21308 :
    PopulationFees20258.bill (n:=21308) (PopulationFees20258.tabulate (21308-1) 256) source080.plan.table+
      4*21308*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*219858574744 := by decide +kernel
private theorem range54From21009To2863 : Segment 54 21009 21308 2816 2863 :=
  paid (pc:=73) (v:=219858574744) (by decide) source080_valid tests54_080_2816 fee54_080_21308 (by decide +kernel)

private theorem range54From21009 : Win 54 21009 21308 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From21009To2402 range54From21009To2468) (join_population range54From21009To2514 range54From21009To2579)) (join_population (join_population range54From21009To2664 range54From21009To2686) (join_population range54From21009To2816 range54From21009To2863)))

private theorem fee54_074_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source074.plan.table+
      4*21640*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*146450909417 := by decide +kernel
private theorem range54From21309To2415 : Segment 54 21309 21640 0 2415 :=
  paid (pc:=77) (v:=146450909417) (by decide) source074_valid tests54_074_0 fee54_074_21640 (by decide +kernel)

private theorem tests54_075_2415 : ∀ z∈source075.plan.table,z.1.Valid 54 2415 := by decide +kernel
private theorem fee54_075_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source075.plan.table+
      4*21640*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*188453809463 := by decide +kernel
private theorem range54From21309To2477 : Segment 54 21309 21640 2415 2477 :=
  paid (pc:=77) (v:=188453809463) (by decide) source075_valid tests54_075_2415 fee54_075_21640 (by decide +kernel)

private theorem tests54_076_2477 : ∀ z∈source076.plan.table,z.1.Valid 54 2477 := by decide +kernel
private theorem fee54_076_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source076.plan.table+
      4*21640*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*234238657544 := by decide +kernel
private theorem range54From21309To2518 : Segment 54 21309 21640 2477 2518 :=
  paid (pc:=77) (v:=234238657544) (by decide) source076_valid tests54_076_2477 fee54_076_21640 (by decide +kernel)

private theorem tests54_077_2518 : ∀ z∈source077.plan.table,z.1.Valid 54 2518 := by decide +kernel
private theorem fee54_077_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source077.plan.table+
      4*21640*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*224184139864 := by decide +kernel
private theorem range54From21309To2582 : Segment 54 21309 21640 2518 2582 :=
  paid (pc:=76) (v:=224184139864) (by decide) source077_valid tests54_077_2518 fee54_077_21640 (by decide +kernel)

private theorem tests54_079_2582 : ∀ z∈source079.plan.table,z.1.Valid 54 2582 := by decide +kernel
private theorem fee54_079_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source079.plan.table+
      4*21640*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*268401625532 := by decide +kernel
private theorem range54From21309To2659 : Segment 54 21309 21640 2582 2659 :=
  paid (pc:=75) (v:=268401625532) (by decide) source079_valid tests54_079_2582 fee54_079_21640 (by decide +kernel)

private theorem tests54_070_2659 : ∀ z∈source070.plan.table,z.1.Valid 54 2659 := by decide +kernel
private theorem fee54_070_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source070.plan.table+
      4*21640*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*208385729380 := by decide +kernel
private theorem range54From21309To2686 : Segment 54 21309 21640 2659 2686 :=
  paid (pc:=75) (v:=208385729380) (by decide) source070_valid tests54_070_2659 fee54_070_21640 (by decide +kernel)

private theorem fee54_073_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source073.plan.table+
      4*21640*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*309739258564 := by decide +kernel
private theorem range54From21309To2798 : Segment 54 21309 21640 2686 2798 :=
  paid (pc:=74) (v:=309739258564) (by decide) source073_valid tests54_073_2686 fee54_073_21640 (by decide +kernel)

private theorem tests54_080_2798 : ∀ z∈source080.plan.table,z.1.Valid 54 2798 := by decide +kernel
private theorem fee54_080_21640 :
    PopulationFees20258.bill (n:=21640) (PopulationFees20258.tabulate (21640-1) 256) source080.plan.table+
      4*21640*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*226307645090 := by decide +kernel
private theorem range54From21309To2863 : Segment 54 21309 21640 2798 2863 :=
  paid (pc:=73) (v:=226307645090) (by decide) source080_valid tests54_080_2798 fee54_080_21640 (by decide +kernel)

private theorem range54From21309 : Win 54 21309 21640 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From21309To2415 range54From21309To2477) (join_population range54From21309To2518 range54From21309To2582)) (join_population (join_population range54From21309To2659 range54From21309To2686) (join_population range54From21309To2798 range54From21309To2863)))

private theorem fee54_074_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source074.plan.table+
      4*22012*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*151057446535 := by decide +kernel
private theorem range54From21641To2428 : Segment 54 21641 22012 0 2428 :=
  paid (pc:=77) (v:=151057446535) (by decide) source074_valid tests54_074_0 fee54_074_22012 (by decide +kernel)

private theorem tests54_076_2428 : ∀ z∈source076.plan.table,z.1.Valid 54 2428 := by decide +kernel
private theorem fee54_076_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source076.plan.table+
      4*22012*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*241536683215 := by decide +kernel
private theorem range54From21641To2522 : Segment 54 21641 22012 2428 2522 :=
  paid (pc:=77) (v:=241536683215) (by decide) source076_valid tests54_076_2428 fee54_076_22012 (by decide +kernel)

private theorem tests54_077_2522 : ∀ z∈source077.plan.table,z.1.Valid 54 2522 := by decide +kernel
private theorem fee54_077_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source077.plan.table+
      4*22012*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*231188581700 := by decide +kernel
private theorem range54From21641To2585 : Segment 54 21641 22012 2522 2585 :=
  paid (pc:=76) (v:=231188581700) (by decide) source077_valid tests54_077_2522 fee54_077_22012 (by decide +kernel)

private theorem tests54_079_2585 : ∀ z∈source079.plan.table,z.1.Valid 54 2585 := by decide +kernel
private theorem fee54_079_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source079.plan.table+
      4*22012*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*276751289778 := by decide +kernel
private theorem range54From21641To2656 : Segment 54 21641 22012 2585 2656 :=
  paid (pc:=76) (v:=276751289778) (by decide) source079_valid tests54_079_2585 fee54_079_22012 (by decide +kernel)

private theorem tests54_070_2656 : ∀ z∈source070.plan.table,z.1.Valid 54 2656 := by decide +kernel
private theorem fee54_070_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source070.plan.table+
      4*22012*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*214966442449 := by decide +kernel
private theorem range54From21641To2686 : Segment 54 21641 22012 2656 2686 :=
  paid (pc:=75) (v:=214966442449) (by decide) source070_valid tests54_070_2656 fee54_070_22012 (by decide +kernel)

private theorem fee54_073_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source073.plan.table+
      4*22012*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*319401849813 := by decide +kernel
private theorem range54From21641To2780 : Segment 54 21641 22012 2686 2780 :=
  paid (pc:=75) (v:=319401849813) (by decide) source073_valid tests54_073_2686 fee54_073_22012 (by decide +kernel)

private theorem tests54_081_2780 : ∀ z∈source081.plan.table,z.1.Valid 54 2780 := by decide +kernel
private theorem fee54_081_22012 :
    PopulationFees20258.bill (n:=22012) (PopulationFees20258.tabulate (22012-1) 256) source081.plan.table+
      4*22012*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*307925151866 := by decide +kernel
private theorem range54From21641To2863 : Segment 54 21641 22012 2780 2863 :=
  paid (pc:=74) (v:=307925151866) (by decide) source081_valid tests54_081_2780 fee54_081_22012 (by decide +kernel)

private theorem range54From21641 : Win 54 21641 22012 :=
  complete (by decide) (by decide) (join_population (join_population range54From21641To2428 (join_population range54From21641To2522 range54From21641To2585)) (join_population (join_population range54From21641To2656 range54From21641To2686) (join_population range54From21641To2780 range54From21641To2863)))

theorem cut54From21009 : Win 54 21009 22012 :=
  (join_ground range54From21009 (join_ground range54From21309 range54From21641))

end JSP233.FiniteCutRanges20258
