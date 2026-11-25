module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source078
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source081
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086
public import Erdos272.Arithmetic.N20258.Sources.Source087

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_25776 :
    PopulationFees20258.bill (n:=25776) (PopulationFees20258.tabulate (25776-1) 256) source082.plan.table+
      4*25776*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*194017688410 := by decide +kernel
private theorem range55From25051To2627 : Segment 55 25051 25776 0 2627 :=
  paid (pc:=77) (v:=194017688410) (by decide) source082_valid tests55_082_0 fee55_082_25776 (by decide +kernel)

private theorem tests55_086_2627 : ∀ z∈source086.plan.table,z.1.Valid 55 2627 := by decide +kernel
private theorem fee55_086_25776 :
    PopulationFees20258.bill (n:=25776) (PopulationFees20258.tabulate (25776-1) 256) source086.plan.table+
      4*25776*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*367079897083 := by decide +kernel
private theorem range55From25051To2740 : Segment 55 25051 25776 2627 2740 :=
  paid (pc:=77) (v:=367079897083) (by decide) source086_valid tests55_086_2627 fee55_086_25776 (by decide +kernel)

private theorem tests55_081_2740 : ∀ z∈source081.plan.table,z.1.Valid 55 2740 := by decide +kernel
private theorem fee55_081_25776 :
    PopulationFees20258.bill (n:=25776) (PopulationFees20258.tabulate (25776-1) 256) source081.plan.table+
      4*25776*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*410234544979 := by decide +kernel
private theorem range55From25051To2860 : Segment 55 25051 25776 2740 2860 :=
  paid (pc:=76) (v:=410234544979) (by decide) source081_valid tests55_081_2740 fee55_081_25776 (by decide +kernel)

private theorem tests55_080_2860 : ∀ z∈source080.plan.table,z.1.Valid 55 2860 := by decide +kernel
private theorem fee55_080_25776 :
    PopulationFees20258.bill (n:=25776) (PopulationFees20258.tabulate (25776-1) 256) source080.plan.table+
      4*25776*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*312365131215 := by decide +kernel
private theorem range55From25051To2968 : Segment 55 25051 25776 2860 2968 :=
  paid (pc:=75) (v:=312365131215) (by decide) source080_valid tests55_080_2860 fee55_080_25776 (by decide +kernel)

private theorem tests55_080_2968 : ∀ z∈source080.plan.table,z.1.Valid 55 2968 := by decide +kernel
private theorem range55From25051To2971 : Segment 55 25051 25776 2968 2971 :=
  paid (pc:=75) (v:=312365131215) (by decide) source080_valid tests55_080_2968 fee55_080_25776 (by decide +kernel)

private theorem range55From25051 : Win 55 25051 25776 :=
  complete (by decide) (by decide) (join_population (join_population range55From25051To2627 range55From25051To2740) (join_population range55From25051To2860 (join_population range55From25051To2968 range55From25051To2971)))

private theorem fee55_082_26623 :
    PopulationFees20258.bill (n:=26623) (PopulationFees20258.tabulate (26623-1) 256) source082.plan.table+
      4*26623*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*206132038952 := by decide +kernel
private theorem range55From25777To2654 : Segment 55 25777 26623 0 2654 :=
  paid (pc:=77) (v:=206132038952) (by decide) source082_valid tests55_082_0 fee55_082_26623 (by decide +kernel)

private theorem tests55_078_2654 : ∀ z∈source078.plan.table,z.1.Valid 55 2654 := by decide +kernel
private theorem fee55_078_26623 :
    PopulationFees20258.bill (n:=26623) (PopulationFees20258.tabulate (26623-1) 256) source078.plan.table+
      4*26623*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*306181911386 := by decide +kernel
private theorem range55From25777To2789 : Segment 55 25777 26623 2654 2789 :=
  paid (pc:=76) (v:=306181911386) (by decide) source078_valid tests55_078_2654 fee55_078_26623 (by decide +kernel)

private theorem tests55_087_2789 : ∀ z∈source087.plan.table,z.1.Valid 55 2789 := by decide +kernel
private theorem fee55_087_26623 :
    PopulationFees20258.bill (n:=26623) (PopulationFees20258.tabulate (26623-1) 256) source087.plan.table+
      4*26623*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*334924907832 := by decide +kernel
private theorem range55From25777To2954 : Segment 55 25777 26623 2789 2954 :=
  paid (pc:=75) (v:=334924907832) (by decide) source087_valid tests55_087_2789 fee55_087_26623 (by decide +kernel)

private theorem tests55_080_2954 : ∀ z∈source080.plan.table,z.1.Valid 55 2954 := by decide +kernel
private theorem fee55_080_26623 :
    PopulationFees20258.bill (n:=26623) (PopulationFees20258.tabulate (26623-1) 256) source080.plan.table+
      4*26623*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*331682566476 := by decide +kernel
private theorem range55From25777To2971 : Segment 55 25777 26623 2954 2971 :=
  paid (pc:=75) (v:=331682566476) (by decide) source080_valid tests55_080_2954 fee55_080_26623 (by decide +kernel)

private theorem range55From25777 : Win 55 25777 26623 :=
  complete (by decide) (by decide) (join_population (join_population range55From25777To2654 range55From25777To2789) (join_population range55From25777To2954 range55From25777To2971))

private theorem fee55_082_27630 :
    PopulationFees20258.bill (n:=27630) (PopulationFees20258.tabulate (27630-1) 256) source082.plan.table+
      4*27630*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*220991671044 := by decide +kernel
private theorem range55From26624To2683 : Segment 55 26624 27630 0 2683 :=
  paid (pc:=77) (v:=220991671044) (by decide) source082_valid tests55_082_0 fee55_082_27630 (by decide +kernel)

private theorem tests55_085_2683 : ∀ z∈source085.plan.table,z.1.Valid 55 2683 := by decide +kernel
private theorem fee55_085_27630 :
    PopulationFees20258.bill (n:=27630) (PopulationFees20258.tabulate (27630-1) 256) source085.plan.table+
      4*27630*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*385947315624 := by decide +kernel
private theorem range55From26624To2863 : Segment 55 26624 27630 2683 2863 :=
  paid (pc:=76) (v:=385947315624) (by decide) source085_valid tests55_085_2683 fee55_085_27630 (by decide +kernel)

private theorem tests55_080_2863 : ∀ z∈source080.plan.table,z.1.Valid 55 2863 := by decide +kernel
private theorem fee55_080_27630 :
    PopulationFees20258.bill (n:=27630) (PopulationFees20258.tabulate (27630-1) 256) source080.plan.table+
      4*27630*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*355404000437 := by decide +kernel
private theorem range55From26624To2970 : Segment 55 26624 27630 2863 2970 :=
  paid (pc:=75) (v:=355404000437) (by decide) source080_valid tests55_080_2863 fee55_080_27630 (by decide +kernel)

private theorem tests55_080_2970 : ∀ z∈source080.plan.table,z.1.Valid 55 2970 := by decide +kernel
private theorem range55From26624To2971 : Segment 55 26624 27630 2970 2971 :=
  paid (pc:=75) (v:=355404000437) (by decide) source080_valid tests55_080_2970 fee55_080_27630 (by decide +kernel)

private theorem range55From26624 : Win 55 26624 27630 :=
  complete (by decide) (by decide) (join_population (join_population range55From26624To2683 range55From26624To2863) (join_population range55From26624To2970 range55From26624To2971))

private theorem fee55_082_28848 :
    PopulationFees20258.bill (n:=28848) (PopulationFees20258.tabulate (28848-1) 256) source082.plan.table+
      4*28848*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*239600687064 := by decide +kernel
private theorem range55From27631To2715 : Segment 55 27631 28848 0 2715 :=
  paid (pc:=77) (v:=239600687064) (by decide) source082_valid tests55_082_0 fee55_082_28848 (by decide +kernel)

private theorem tests55_085_2715 : ∀ z∈source085.plan.table,z.1.Valid 55 2715 := by decide +kernel
private theorem fee55_085_28848 :
    PopulationFees20258.bill (n:=28848) (PopulationFees20258.tabulate (28848-1) 256) source085.plan.table+
      4*28848*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*418026091183 := by decide +kernel
private theorem range55From27631To2870 : Segment 55 27631 28848 2715 2870 :=
  paid (pc:=76) (v:=418026091183) (by decide) source085_valid tests55_085_2715 fee55_085_28848 (by decide +kernel)

private theorem tests55_080_2870 : ∀ z∈source080.plan.table,z.1.Valid 55 2870 := by decide +kernel
private theorem fee55_080_28848 :
    PopulationFees20258.bill (n:=28848) (PopulationFees20258.tabulate (28848-1) 256) source080.plan.table+
      4*28848*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*385229208773 := by decide +kernel
private theorem range55From27631To2970 : Segment 55 27631 28848 2870 2970 :=
  paid (pc:=75) (v:=385229208773) (by decide) source080_valid tests55_080_2870 fee55_080_28848 (by decide +kernel)

private theorem range55From27631To2971 : Segment 55 27631 28848 2970 2971 :=
  paid (pc:=75) (v:=385229208773) (by decide) source080_valid tests55_080_2970 fee55_080_28848 (by decide +kernel)

private theorem range55From27631 : Win 55 27631 28848 :=
  complete (by decide) (by decide) (join_population (join_population range55From27631To2715 range55From27631To2870) (join_population range55From27631To2970 range55From27631To2971))

private theorem fee55_082_30354 :
    PopulationFees20258.bill (n:=30354) (PopulationFees20258.tabulate (30354-1) 256) source082.plan.table+
      4*30354*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*263760099597 := by decide +kernel
private theorem range55From28849To2747 : Segment 55 28849 30354 0 2747 :=
  paid (pc:=77) (v:=263760099597) (by decide) source082_valid tests55_082_0 fee55_082_30354 (by decide +kernel)

private theorem tests55_085_2747 : ∀ z∈source085.plan.table,z.1.Valid 55 2747 := by decide +kernel
private theorem fee55_085_30354 :
    PopulationFees20258.bill (n:=30354) (PopulationFees20258.tabulate (30354-1) 256) source085.plan.table+
      4*30354*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*459609387822 := by decide +kernel
private theorem range55From28849To2874 : Segment 55 28849 30354 2747 2874 :=
  paid (pc:=76) (v:=459609387822) (by decide) source085_valid tests55_085_2747 fee55_085_30354 (by decide +kernel)

private theorem tests55_080_2874 : ∀ z∈source080.plan.table,z.1.Valid 55 2874 := by decide +kernel
private theorem fee55_080_30354 :
    PopulationFees20258.bill (n:=30354) (PopulationFees20258.tabulate (30354-1) 256) source080.plan.table+
      4*30354*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*423635447661 := by decide +kernel
private theorem range55From28849To2969 : Segment 55 28849 30354 2874 2969 :=
  paid (pc:=75) (v:=423635447661) (by decide) source080_valid tests55_080_2874 fee55_080_30354 (by decide +kernel)

private theorem tests55_080_2969 : ∀ z∈source080.plan.table,z.1.Valid 55 2969 := by decide +kernel
private theorem range55From28849To2971 : Segment 55 28849 30354 2969 2971 :=
  paid (pc:=75) (v:=423635447661) (by decide) source080_valid tests55_080_2969 fee55_080_30354 (by decide +kernel)

private theorem range55From28849 : Win 55 28849 30354 :=
  complete (by decide) (by decide) (join_population (join_population range55From28849To2747 range55From28849To2874) (join_population range55From28849To2969 range55From28849To2971))

theorem cut55From25051 : Win 55 25051 30354 :=
  (join_ground (join_ground range55From25051 range55From25777) (join_ground range55From26624 (join_ground range55From27631 range55From28849)))

end JSP233.FiniteCutRanges20258
