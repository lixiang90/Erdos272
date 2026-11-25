module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source070
public import Erdos272.Arithmetic.N20258.Sources.Source073
public import Erdos272.Arithmetic.N20258.Sources.Source074
public import Erdos272.Arithmetic.N20258.Sources.Source076
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
private theorem fee54_074_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source074.plan.table+
      4*22433*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*156359830959 := by decide +kernel
private theorem range54From22013To2442 : Segment 54 22013 22433 0 2442 :=
  paid (pc:=77) (v:=156359830959) (by decide) source074_valid tests54_074_0 fee54_074_22433 (by decide +kernel)

private theorem tests54_076_2442 : ∀ z∈source076.plan.table,z.1.Valid 54 2442 := by decide +kernel
private theorem fee54_076_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source076.plan.table+
      4*22433*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*249926628409 := by decide +kernel
private theorem range54From22013To2529 : Segment 54 22013 22433 2442 2529 :=
  paid (pc:=77) (v:=249926628409) (by decide) source076_valid tests54_076_2442 fee54_076_22433 (by decide +kernel)

private theorem tests54_077_2529 : ∀ z∈source077.plan.table,z.1.Valid 54 2529 := by decide +kernel
private theorem fee54_077_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source077.plan.table+
      4*22433*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*239234460268 := by decide +kernel
private theorem range54From22013To2589 : Segment 54 22013 22433 2529 2589 :=
  paid (pc:=76) (v:=239234460268) (by decide) source077_valid tests54_077_2529 fee54_077_22433 (by decide +kernel)

private theorem tests54_079_2589 : ∀ z∈source079.plan.table,z.1.Valid 54 2589 := by decide +kernel
private theorem fee54_079_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source079.plan.table+
      4*22433*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*286339596040 := by decide +kernel
private theorem range54From22013To2653 : Segment 54 22013 22433 2589 2653 :=
  paid (pc:=76) (v:=286339596040) (by decide) source079_valid tests54_079_2589 fee54_079_22433 (by decide +kernel)

private theorem tests54_078_2653 : ∀ z∈source078.plan.table,z.1.Valid 54 2653 := by decide +kernel
private theorem fee54_078_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source078.plan.table+
      4*22433*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*223069398861 := by decide +kernel
private theorem range54From22013To2683 : Segment 54 22013 22433 2653 2683 :=
  paid (pc:=76) (v:=223069398861) (by decide) source078_valid tests54_078_2653 fee54_078_22433 (by decide +kernel)

private theorem tests54_070_2683 : ∀ z∈source070.plan.table,z.1.Valid 54 2683 := by decide +kernel
private theorem fee54_070_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source070.plan.table+
      4*22433*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*222619016299 := by decide +kernel
private theorem range54From22013To2686 : Segment 54 22013 22433 2683 2686 :=
  paid (pc:=76) (v:=222619016299) (by decide) source070_valid tests54_070_2683 fee54_070_22433 (by decide +kernel)

private theorem tests54_073_2686 : ∀ z∈source073.plan.table,z.1.Valid 54 2686 := by decide +kernel
private theorem fee54_073_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source073.plan.table+
      4*22433*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*330539456667 := by decide +kernel
private theorem range54From22013To2763 : Segment 54 22013 22433 2686 2763 :=
  paid (pc:=75) (v:=330539456667) (by decide) source073_valid tests54_073_2686 fee54_073_22433 (by decide +kernel)

private theorem tests54_081_2763 : ∀ z∈source081.plan.table,z.1.Valid 54 2763 := by decide +kernel
private theorem fee54_081_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source081.plan.table+
      4*22433*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*318580376457 := by decide +kernel
private theorem range54From22013To2861 : Segment 54 22013 22433 2763 2861 :=
  paid (pc:=74) (v:=318580376457) (by decide) source081_valid tests54_081_2763 fee54_081_22433 (by decide +kernel)

private theorem tests54_080_2861 : ∀ z∈source080.plan.table,z.1.Valid 54 2861 := by decide +kernel
private theorem fee54_080_22433 :
    PopulationFees20258.bill (n:=22433) (PopulationFees20258.tabulate (22433-1) 256) source080.plan.table+
      4*22433*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*241643744037 := by decide +kernel
private theorem range54From22013To2863 : Segment 54 22013 22433 2861 2863 :=
  paid (pc:=74) (v:=241643744037) (by decide) source080_valid tests54_080_2861 fee54_080_22433 (by decide +kernel)

private theorem range54From22013 : Win 54 22013 22433 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From22013To2442 range54From22013To2529) (join_population range54From22013To2589 range54From22013To2653)) (join_population (join_population range54From22013To2683 range54From22013To2686) (join_population range54From22013To2763 (join_population range54From22013To2861 range54From22013To2863))))

private theorem fee54_074_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source074.plan.table+
      4*22916*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*162646114915 := by decide +kernel
private theorem range54From22434To2457 : Segment 54 22434 22916 0 2457 :=
  paid (pc:=77) (v:=162646114915) (by decide) source074_valid tests54_074_0 fee54_074_22916 (by decide +kernel)

private theorem tests54_076_2457 : ∀ z∈source076.plan.table,z.1.Valid 54 2457 := by decide +kernel
private theorem fee54_076_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source076.plan.table+
      4*22916*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*259854481027 := by decide +kernel
private theorem range54From22434To2535 : Segment 54 22434 22916 2457 2535 :=
  paid (pc:=77) (v:=259854481027) (by decide) source076_valid tests54_076_2457 fee54_076_22916 (by decide +kernel)

private theorem tests54_077_2535 : ∀ z∈source077.plan.table,z.1.Valid 54 2535 := by decide +kernel
private theorem fee54_077_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source077.plan.table+
      4*22916*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*248754056520 := by decide +kernel
private theorem range54From22434To2592 : Segment 54 22434 22916 2535 2592 :=
  paid (pc:=76) (v:=248754056520) (by decide) source077_valid tests54_077_2535 fee54_077_22916 (by decide +kernel)

private theorem tests54_079_2592 : ∀ z∈source079.plan.table,z.1.Valid 54 2592 := by decide +kernel
private theorem fee54_079_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source079.plan.table+
      4*22916*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*297691320343 := by decide +kernel
private theorem range54From22434To2648 : Segment 54 22434 22916 2592 2648 :=
  paid (pc:=76) (v:=297691320343) (by decide) source079_valid tests54_079_2592 fee54_079_22916 (by decide +kernel)

private theorem tests54_078_2648 : ∀ z∈source078.plan.table,z.1.Valid 54 2648 := by decide +kernel
private theorem fee54_078_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source078.plan.table+
      4*22916*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*232035245458 := by decide +kernel
private theorem range54From22434To2682 : Segment 54 22434 22916 2648 2682 :=
  paid (pc:=76) (v:=232035245458) (by decide) source078_valid tests54_078_2648 fee54_078_22916 (by decide +kernel)

private theorem tests54_070_2682 : ∀ z∈source070.plan.table,z.1.Valid 54 2682 := by decide +kernel
private theorem fee54_070_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source070.plan.table+
      4*22916*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*231523469017 := by decide +kernel
private theorem range54From22434To2686 : Segment 54 22434 22916 2682 2686 :=
  paid (pc:=76) (v:=231523469017) (by decide) source070_valid tests54_070_2682 fee54_070_22916 (by decide +kernel)

private theorem fee54_073_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source073.plan.table+
      4*22916*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*343539317451 := by decide +kernel
private theorem range54From22434To2746 : Segment 54 22434 22916 2686 2746 :=
  paid (pc:=75) (v:=343539317451) (by decide) source073_valid tests54_073_2686 fee54_073_22916 (by decide +kernel)

private theorem tests54_081_2746 : ∀ z∈source081.plan.table,z.1.Valid 54 2746 := by decide +kernel
private theorem fee54_081_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source081.plan.table+
      4*22916*NaturalPopulation20258.weights source081.extras≤source081.plan.scale*331186257384 := by decide +kernel
private theorem range54From22434To2835 : Segment 54 22434 22916 2746 2835 :=
  paid (pc:=74) (v:=331186257384) (by decide) source081_valid tests54_081_2746 fee54_081_22916 (by decide +kernel)

private theorem tests54_080_2835 : ∀ z∈source080.plan.table,z.1.Valid 54 2835 := by decide +kernel
private theorem fee54_080_22916 :
    PopulationFees20258.bill (n:=22916) (PopulationFees20258.tabulate (22916-1) 256) source080.plan.table+
      4*22916*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*251341707907 := by decide +kernel
private theorem range54From22434To2863 : Segment 54 22434 22916 2835 2863 :=
  paid (pc:=74) (v:=251341707907) (by decide) source080_valid tests54_080_2835 fee54_080_22916 (by decide +kernel)

private theorem range54From22434 : Win 54 22434 22916 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From22434To2457 range54From22434To2535) (join_population range54From22434To2592 range54From22434To2648)) (join_population (join_population range54From22434To2682 range54From22434To2686) (join_population range54From22434To2746 (join_population range54From22434To2835 range54From22434To2863))))

theorem cut54From22013 : Win 54 22013 22916 :=
  (join_ground range54From22013 range54From22434)

end JSP233.FiniteCutRanges20258
