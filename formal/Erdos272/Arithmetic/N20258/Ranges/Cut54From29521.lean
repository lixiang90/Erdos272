module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source062
public import Erdos272.Arithmetic.N20258.Sources.Source069
public import Erdos272.Arithmetic.N20258.Sources.Source070
public import Erdos272.Arithmetic.N20258.Sources.Source074
public import Erdos272.Arithmetic.N20258.Sources.Source080

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests54_074_0 : ∀ z∈source074.plan.table,z.1.Valid 54 0 := by decide +kernel
private theorem fee54_074_31524 :
    PopulationFees20258.bill (n:=31524) (PopulationFees20258.tabulate (31524-1) 256) source074.plan.table+
      4*31524*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*294300907686 := by decide +kernel
private theorem range54From29521To2660 : Segment 54 29521 31524 0 2660 :=
  paid (pc:=76) (v:=294300907686) (by decide) source074_valid tests54_074_0 fee54_074_31524 (by decide +kernel)

private theorem tests54_070_2660 : ∀ z∈source070.plan.table,z.1.Valid 54 2660 := by decide +kernel
private theorem fee54_070_31524 :
    PopulationFees20258.bill (n:=31524) (PopulationFees20258.tabulate (31524-1) 256) source070.plan.table+
      4*31524*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*419732033201 := by decide +kernel
private theorem range54From29521To2744 : Segment 54 29521 31524 2660 2744 :=
  paid (pc:=75) (v:=419732033201) (by decide) source070_valid tests54_070_2660 fee54_070_31524 (by decide +kernel)

private theorem tests54_069_2744 : ∀ z∈source069.plan.table,z.1.Valid 54 2744 := by decide +kernel
private theorem fee54_069_31524 :
    PopulationFees20258.bill (n:=31524) (PopulationFees20258.tabulate (31524-1) 256) source069.plan.table+
      4*31524*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*397341688819 := by decide +kernel
private theorem range54From29521To2794 : Segment 54 29521 31524 2744 2794 :=
  paid (pc:=75) (v:=397341688819) (by decide) source069_valid tests54_069_2744 fee54_069_31524 (by decide +kernel)

private theorem tests54_080_2794 : ∀ z∈source080.plan.table,z.1.Valid 54 2794 := by decide +kernel
private theorem fee54_080_31524 :
    PopulationFees20258.bill (n:=31524) (PopulationFees20258.tabulate (31524-1) 256) source080.plan.table+
      4*31524*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*455029734351 := by decide +kernel
private theorem range54From29521To2862 : Segment 54 29521 31524 2794 2862 :=
  paid (pc:=75) (v:=455029734351) (by decide) source080_valid tests54_080_2794 fee54_080_31524 (by decide +kernel)

private theorem tests54_080_2862 : ∀ z∈source080.plan.table,z.1.Valid 54 2862 := by decide +kernel
private theorem range54From29521To2863 : Segment 54 29521 31524 2862 2863 :=
  paid (pc:=75) (v:=455029734351) (by decide) source080_valid tests54_080_2862 fee54_080_31524 (by decide +kernel)

private theorem range54From29521 : Win 54 29521 31524 :=
  complete (by decide) (by decide) (join_population (join_population range54From29521To2660 range54From29521To2744) (join_population range54From29521To2794 (join_population range54From29521To2862 range54From29521To2863)))

private theorem fee54_074_34112 :
    PopulationFees20258.bill (n:=34112) (PopulationFees20258.tabulate (34112-1) 256) source074.plan.table+
      4*34112*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*341266080002 := by decide +kernel
private theorem range54From31525To2702 : Segment 54 31525 34112 0 2702 :=
  paid (pc:=75) (v:=341266080002) (by decide) source074_valid tests54_074_0 fee54_074_34112 (by decide +kernel)

private theorem tests54_062_2702 : ∀ z∈source062.plan.table,z.1.Valid 54 2702 := by decide +kernel
private theorem fee54_062_34112 :
    PopulationFees20258.bill (n:=34112) (PopulationFees20258.tabulate (34112-1) 256) source062.plan.table+
      4*34112*NaturalPopulation20258.weights source062.extras≤source062.plan.scale*483789161266 := by decide +kernel
private theorem range54From31525To2769 : Segment 54 31525 34112 2702 2769 :=
  paid (pc:=75) (v:=483789161266) (by decide) source062_valid tests54_062_2702 fee54_062_34112 (by decide +kernel)

private theorem tests54_069_2769 : ∀ z∈source069.plan.table,z.1.Valid 54 2769 := by decide +kernel
private theorem fee54_069_34112 :
    PopulationFees20258.bill (n:=34112) (PopulationFees20258.tabulate (34112-1) 256) source069.plan.table+
      4*34112*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*461145843762 := by decide +kernel
private theorem range54From31525To2809 : Segment 54 31525 34112 2769 2809 :=
  paid (pc:=75) (v:=461145843762) (by decide) source069_valid tests54_069_2769 fee54_069_34112 (by decide +kernel)

private theorem tests54_080_2809 : ∀ z∈source080.plan.table,z.1.Valid 54 2809 := by decide +kernel
private theorem fee54_080_34112 :
    PopulationFees20258.bill (n:=34112) (PopulationFees20258.tabulate (34112-1) 256) source080.plan.table+
      4*34112*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*527703312380 := by decide +kernel
private theorem range54From31525To2862 : Segment 54 31525 34112 2809 2862 :=
  paid (pc:=74) (v:=527703312380) (by decide) source080_valid tests54_080_2809 fee54_080_34112 (by decide +kernel)

private theorem range54From31525To2863 : Segment 54 31525 34112 2862 2863 :=
  paid (pc:=74) (v:=527703312380) (by decide) source080_valid tests54_080_2862 fee54_080_34112 (by decide +kernel)

private theorem range54From31525 : Win 54 31525 34112 :=
  complete (by decide) (by decide) (join_population (join_population range54From31525To2702 range54From31525To2769) (join_population range54From31525To2809 (join_population range54From31525To2862 range54From31525To2863)))

private theorem range54From34113 : Win 54 34113 39999 :=
  short (by decide) (by decide)

theorem cut54From29521 : Win 54 29521 39999 :=
  (join_ground range54From29521 (join_ground range54From31525 range54From34113))

end JSP233.FiniteCutRanges20258
