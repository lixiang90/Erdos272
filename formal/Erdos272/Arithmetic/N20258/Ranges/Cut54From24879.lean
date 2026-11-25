module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source066
public import Erdos272.Arithmetic.N20258.Sources.Source069
public import Erdos272.Arithmetic.N20258.Sources.Source070
public import Erdos272.Arithmetic.N20258.Sources.Source074
public import Erdos272.Arithmetic.N20258.Sources.Source077
public import Erdos272.Arithmetic.N20258.Sources.Source078
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
private theorem fee54_074_25728 :
    PopulationFees20258.bill (n:=25728) (PopulationFees20258.tabulate (25728-1) 256) source074.plan.table+
      4*25728*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*201348388622 := by decide +kernel
private theorem range54From24879To2554 : Segment 54 24879 25728 0 2554 :=
  paid (pc:=77) (v:=201348388622) (by decide) source074_valid tests54_074_0 fee54_074_25728 (by decide +kernel)

private theorem tests54_077_2554 : ∀ z∈source077.plan.table,z.1.Valid 54 2554 := by decide +kernel
private theorem fee54_077_25728 :
    PopulationFees20258.bill (n:=25728) (PopulationFees20258.tabulate (25728-1) 256) source077.plan.table+
      4*25728*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*307368901365 := by decide +kernel
private theorem range54From24879To2643 : Segment 54 24879 25728 2554 2643 :=
  paid (pc:=77) (v:=307368901365) (by decide) source077_valid tests54_077_2554 fee54_077_25728 (by decide +kernel)

private theorem tests54_078_2643 : ∀ z∈source078.plan.table,z.1.Valid 54 2643 := by decide +kernel
private theorem fee54_078_25728 :
    PopulationFees20258.bill (n:=25728) (PopulationFees20258.tabulate (25728-1) 256) source078.plan.table+
      4*25728*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*287282139631 := by decide +kernel
private theorem range54From24879To2718 : Segment 54 24879 25728 2643 2718 :=
  paid (pc:=76) (v:=287282139631) (by decide) source078_valid tests54_078_2643 fee54_078_25728 (by decide +kernel)

private theorem tests54_081_2718 : ∀ z∈source081.plan.table,z.1.Valid 54 2718 := by decide +kernel
private theorem fee54_081_25728 :
    PopulationFees20258.bill (n:=25728) (PopulationFees20258.tabulate (25728-1) 256) source081.plan.table+
      4*25728*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*408766412414 := by decide +kernel
private theorem range54From24879To2792 : Segment 54 24879 25728 2718 2792 :=
  paid (pc:=76) (v:=408766412414) (by decide) source081_valid tests54_081_2718 fee54_081_25728 (by decide +kernel)

private theorem tests54_081_2792 : ∀ z∈source081.plan.table,z.1.Valid 54 2792 := by decide +kernel
private theorem range54From24879To2794 : Segment 54 24879 25728 2792 2794 :=
  paid (pc:=76) (v:=408766412414) (by decide) source081_valid tests54_081_2792 fee54_081_25728 (by decide +kernel)

private theorem tests54_080_2794 : ∀ z∈source080.plan.table,z.1.Valid 54 2794 := by decide +kernel
private theorem fee54_080_25728 :
    PopulationFees20258.bill (n:=25728) (PopulationFees20258.tabulate (25728-1) 256) source080.plan.table+
      4*25728*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*311222561962 := by decide +kernel
private theorem range54From24879To2863 : Segment 54 24879 25728 2794 2863 :=
  paid (pc:=75) (v:=311222561962) (by decide) source080_valid tests54_080_2794 fee54_080_25728 (by decide +kernel)

private theorem range54From24879 : Win 54 24879 25728 :=
  complete (by decide) (by decide) (join_population (join_population range54From24879To2554 (join_population range54From24879To2643 range54From24879To2718)) (join_population range54From24879To2792 (join_population range54From24879To2794 range54From24879To2863)))

private theorem fee54_074_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source074.plan.table+
      4*26726*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*216111175108 := by decide +kernel
private theorem range54From25729To2585 : Segment 54 25729 26726 0 2585 :=
  paid (pc:=77) (v:=216111175108) (by decide) source074_valid tests54_074_0 fee54_074_26726 (by decide +kernel)

private theorem tests54_079_2585 : ∀ z∈source079.plan.table,z.1.Valid 54 2585 := by decide +kernel
private theorem fee54_079_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source079.plan.table+
      4*26726*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*394187418922 := by decide +kernel
private theorem range54From25729To2681 : Segment 54 25729 26726 2585 2681 :=
  paid (pc:=76) (v:=394187418922) (by decide) source079_valid tests54_079_2585 fee54_079_26726 (by decide +kernel)

private theorem tests54_070_2681 : ∀ z∈source070.plan.table,z.1.Valid 54 2681 := by decide +kernel
private theorem fee54_070_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source070.plan.table+
      4*26726*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*308042814148 := by decide +kernel
private theorem range54From25729To2736 : Segment 54 25729 26726 2681 2736 :=
  paid (pc:=76) (v:=308042814148) (by decide) source070_valid tests54_070_2681 fee54_070_26726 (by decide +kernel)

private theorem tests54_081_2736 : ∀ z∈source081.plan.table,z.1.Valid 54 2736 := by decide +kernel
private theorem fee54_081_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source081.plan.table+
      4*26726*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*438304162465 := by decide +kernel
private theorem range54From25729To2790 : Segment 54 25729 26726 2736 2790 :=
  paid (pc:=76) (v:=438304162465) (by decide) source081_valid tests54_081_2736 fee54_081_26726 (by decide +kernel)

private theorem tests54_069_2790 : ∀ z∈source069.plan.table,z.1.Valid 54 2790 := by decide +kernel
private theorem fee54_069_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source069.plan.table+
      4*26726*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*291342384717 := by decide +kernel
private theorem range54From25729To2794 : Segment 54 25729 26726 2790 2794 :=
  paid (pc:=76) (v:=291342384717) (by decide) source069_valid tests54_069_2790 fee54_069_26726 (by decide +kernel)

private theorem fee54_080_26726 :
    PopulationFees20258.bill (n:=26726) (PopulationFees20258.tabulate (26726-1) 256) source080.plan.table+
      4*26726*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*334056214950 := by decide +kernel
private theorem range54From25729To2863 : Segment 54 25729 26726 2794 2863 :=
  paid (pc:=75) (v:=334056214950) (by decide) source080_valid tests54_080_2794 fee54_080_26726 (by decide +kernel)

private theorem range54From25729 : Win 54 25729 26726 :=
  complete (by decide) (by decide) (join_population (join_population range54From25729To2585 (join_population range54From25729To2681 range54From25729To2736)) (join_population range54From25729To2790 (join_population range54From25729To2794 range54From25729To2863)))

private theorem fee54_074_27961 :
    PopulationFees20258.bill (n:=27961) (PopulationFees20258.tabulate (27961-1) 256) source074.plan.table+
      4*27961*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*235059847158 := by decide +kernel
private theorem range54From26727To2607 : Segment 54 26727 27961 0 2607 :=
  paid (pc:=77) (v:=235059847158) (by decide) source074_valid tests54_074_0 fee54_074_27961 (by decide +kernel)

private theorem tests54_078_2607 : ∀ z∈source078.plan.table,z.1.Valid 54 2607 := by decide +kernel
private theorem fee54_078_27961 :
    PopulationFees20258.bill (n:=27961) (PopulationFees20258.tabulate (27961-1) 256) source078.plan.table+
      4*27961*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*335416530021 := by decide +kernel
private theorem range54From26727To2736 : Segment 54 26727 27961 2607 2736 :=
  paid (pc:=76) (v:=335416530021) (by decide) source078_valid tests54_078_2607 fee54_078_27961 (by decide +kernel)

private theorem tests54_066_2736 : ∀ z∈source066.plan.table,z.1.Valid 54 2736 := by decide +kernel
private theorem fee54_066_27961 :
    PopulationFees20258.bill (n:=27961) (PopulationFees20258.tabulate (27961-1) 256) source066.plan.table+
      4*27961*NaturalPopulation20258.weights source066.extras≤source066.plan.scale*322821590509 := by decide +kernel
private theorem range54From26727To2775 : Segment 54 26727 27961 2736 2775 :=
  paid (pc:=76) (v:=322821590509) (by decide) source066_valid tests54_066_2736 fee54_066_27961 (by decide +kernel)

private theorem tests54_069_2775 : ∀ z∈source069.plan.table,z.1.Valid 54 2775 := by decide +kernel
private theorem fee54_069_27961 :
    PopulationFees20258.bill (n:=27961) (PopulationFees20258.tabulate (27961-1) 256) source069.plan.table+
      4*27961*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*316995465803 := by decide +kernel
private theorem range54From26727To2794 : Segment 54 26727 27961 2775 2794 :=
  paid (pc:=76) (v:=316995465803) (by decide) source069_valid tests54_069_2775 fee54_069_27961 (by decide +kernel)

private theorem fee54_080_27961 :
    PopulationFees20258.bill (n:=27961) (PopulationFees20258.tabulate (27961-1) 256) source080.plan.table+
      4*27961*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*363368272873 := by decide +kernel
private theorem range54From26727To2863 : Segment 54 26727 27961 2794 2863 :=
  paid (pc:=75) (v:=363368272873) (by decide) source080_valid tests54_080_2794 fee54_080_27961 (by decide +kernel)

private theorem range54From26727 : Win 54 26727 27961 :=
  complete (by decide) (by decide) (join_population (join_population range54From26727To2607 range54From26727To2736) (join_population range54From26727To2775 (join_population range54From26727To2794 range54From26727To2863)))

private theorem fee54_074_29520 :
    PopulationFees20258.bill (n:=29520) (PopulationFees20258.tabulate (29520-1) 256) source074.plan.table+
      4*29520*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*260099061351 := by decide +kernel
private theorem range54From27962To2632 : Segment 54 27962 29520 0 2632 :=
  paid (pc:=76) (v:=260099061351) (by decide) source074_valid tests54_074_0 fee54_074_29520 (by decide +kernel)

private theorem tests54_078_2632 : ∀ z∈source078.plan.table,z.1.Valid 54 2632 := by decide +kernel
private theorem fee54_078_29520 :
    PopulationFees20258.bill (n:=29520) (PopulationFees20258.tabulate (29520-1) 256) source078.plan.table+
      4*29520*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*371163658097 := by decide +kernel
private theorem range54From27962To2739 : Segment 54 27962 29520 2632 2739 :=
  paid (pc:=76) (v:=371163658097) (by decide) source078_valid tests54_078_2632 fee54_078_29520 (by decide +kernel)

private theorem tests54_066_2739 : ∀ z∈source066.plan.table,z.1.Valid 54 2739 := by decide +kernel
private theorem fee54_066_29520 :
    PopulationFees20258.bill (n:=29520) (PopulationFees20258.tabulate (29520-1) 256) source066.plan.table+
      4*29520*NaturalPopulation20258.weights source066.extras≤source066.plan.scale*357375104055 := by decide +kernel
private theorem range54From27962To2776 : Segment 54 27962 29520 2739 2776 :=
  paid (pc:=75) (v:=357375104055) (by decide) source066_valid tests54_066_2739 fee54_066_29520 (by decide +kernel)

private theorem tests54_069_2776 : ∀ z∈source069.plan.table,z.1.Valid 54 2776 := by decide +kernel
private theorem fee54_069_29520 :
    PopulationFees20258.bill (n:=29520) (PopulationFees20258.tabulate (29520-1) 256) source069.plan.table+
      4*29520*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*350965156918 := by decide +kernel
private theorem range54From27962To2794 : Segment 54 27962 29520 2776 2794 :=
  paid (pc:=75) (v:=350965156918) (by decide) source069_valid tests54_069_2776 fee54_069_29520 (by decide +kernel)

private theorem fee54_080_29520 :
    PopulationFees20258.bill (n:=29520) (PopulationFees20258.tabulate (29520-1) 256) source080.plan.table+
      4*29520*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*402118523103 := by decide +kernel
private theorem range54From27962To2863 : Segment 54 27962 29520 2794 2863 :=
  paid (pc:=75) (v:=402118523103) (by decide) source080_valid tests54_080_2794 fee54_080_29520 (by decide +kernel)

private theorem range54From27962 : Win 54 27962 29520 :=
  complete (by decide) (by decide) (join_population (join_population range54From27962To2632 range54From27962To2739) (join_population range54From27962To2776 (join_population range54From27962To2794 range54From27962To2863)))

theorem cut54From24879 : Win 54 24879 29520 :=
  (join_ground (join_ground range54From24879 range54From25729) (join_ground range54From26727 range54From27962))

end JSP233.FiniteCutRanges20258
