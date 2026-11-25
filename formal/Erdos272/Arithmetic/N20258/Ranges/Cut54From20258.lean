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

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests54_074_0 : ∀ z∈source074.plan.table,z.1.Valid 54 0 := by decide +kernel
private theorem fee54_074_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source074.plan.table+
      4*20488*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*132405438209 := by decide +kernel
private theorem range54From20258To2369 : Segment 54 20258 20488 0 2369 :=
  paid (pc:=77) (v:=132405438209) (by decide) source074_valid tests54_074_0 fee54_074_20488 (by decide +kernel)

private theorem tests54_075_2369 : ∀ z∈source075.plan.table,z.1.Valid 54 2369 := by decide +kernel
private theorem fee54_075_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source075.plan.table+
      4*20488*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*170505038595 := by decide +kernel
private theorem range54From20258To2443 : Segment 54 20258 20488 2369 2443 :=
  paid (pc:=77) (v:=170505038595) (by decide) source075_valid tests54_075_2369 fee54_075_20488 (by decide +kernel)

private theorem tests54_076_2443 : ∀ z∈source076.plan.table,z.1.Valid 54 2443 := by decide +kernel
private theorem fee54_076_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source076.plan.table+
      4*20488*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*212027352370 := by decide +kernel
private theorem range54From20258To2501 : Segment 54 20258 20488 2443 2501 :=
  paid (pc:=76) (v:=212027352370) (by decide) source076_valid tests54_076_2443 fee54_076_20488 (by decide +kernel)

private theorem tests54_077_2501 : ∀ z∈source077.plan.table,z.1.Valid 54 2501 := by decide +kernel
private theorem fee54_077_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source077.plan.table+
      4*20488*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*202903976758 := by decide +kernel
private theorem range54From20258To2570 : Segment 54 20258 20488 2501 2570 :=
  paid (pc:=76) (v:=202903976758) (by decide) source077_valid tests54_077_2501 fee54_077_20488 (by decide +kernel)

private theorem tests54_079_2570 : ∀ z∈source079.plan.table,z.1.Valid 54 2570 := by decide +kernel
private theorem fee54_079_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source079.plan.table+
      4*20488*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*243015587116 := by decide +kernel
private theorem range54From20258To2676 : Segment 54 20258 20488 2570 2676 :=
  paid (pc:=75) (v:=243015587116) (by decide) source079_valid tests54_079_2570 fee54_079_20488 (by decide +kernel)

private theorem tests54_070_2676 : ∀ z∈source070.plan.table,z.1.Valid 54 2676 := by decide +kernel
private theorem fee54_070_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source070.plan.table+
      4*20488*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*188446551549 := by decide +kernel
private theorem range54From20258To2686 : Segment 54 20258 20488 2676 2686 :=
  paid (pc:=74) (v:=188446551549) (by decide) source070_valid tests54_070_2676 fee54_070_20488 (by decide +kernel)

private theorem tests54_073_2686 : ∀ z∈source073.plan.table,z.1.Valid 54 2686 := by decide +kernel
private theorem fee54_073_20488 :
    PopulationFees20258.bill (n:=20488) (PopulationFees20258.tabulate (20488-1) 256) source073.plan.table+
      4*20488*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*280662606728 := by decide +kernel
private theorem range54From20258To2863 : Segment 54 20258 20488 2686 2863 :=
  paid (pc:=73) (v:=280662606728) (by decide) source073_valid tests54_073_2686 fee54_073_20488 (by decide +kernel)

private theorem range54From20258 : Win 54 20258 20488 :=
  complete (by decide) (by decide) (join_population (join_population range54From20258To2369 (join_population range54From20258To2443 range54From20258To2501)) (join_population (join_population range54From20258To2570 range54From20258To2676) (join_population range54From20258To2686 range54From20258To2863)))

private theorem fee54_074_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source074.plan.table+
      4*20736*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*135393506055 := by decide +kernel
private theorem range54From20489To2380 : Segment 54 20489 20736 0 2380 :=
  paid (pc:=77) (v:=135393506055) (by decide) source074_valid tests54_074_0 fee54_074_20736 (by decide +kernel)

private theorem tests54_075_2380 : ∀ z∈source075.plan.table,z.1.Valid 54 2380 := by decide +kernel
private theorem fee54_075_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source075.plan.table+
      4*20736*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*174316014785 := by decide +kernel
private theorem range54From20489To2452 : Segment 54 20489 20736 2380 2452 :=
  paid (pc:=77) (v:=174316014785) (by decide) source075_valid tests54_075_2380 fee54_075_20736 (by decide +kernel)

private theorem tests54_076_2452 : ∀ z∈source076.plan.table,z.1.Valid 54 2452 := by decide +kernel
private theorem fee54_076_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source076.plan.table+
      4*20736*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*216764384175 := by decide +kernel
private theorem range54From20489To2506 : Segment 54 20489 20736 2452 2506 :=
  paid (pc:=76) (v:=216764384175) (by decide) source076_valid tests54_076_2452 fee54_076_20736 (by decide +kernel)

private theorem tests54_077_2506 : ∀ z∈source077.plan.table,z.1.Valid 54 2506 := by decide +kernel
private theorem fee54_077_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source077.plan.table+
      4*20736*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*207422884345 := by decide +kernel
private theorem range54From20489To2574 : Segment 54 20489 20736 2506 2574 :=
  paid (pc:=76) (v:=207422884345) (by decide) source077_valid tests54_077_2506 fee54_077_20736 (by decide +kernel)

private theorem tests54_079_2574 : ∀ z∈source079.plan.table,z.1.Valid 54 2574 := by decide +kernel
private theorem fee54_079_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source079.plan.table+
      4*20736*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*248415661806 := by decide +kernel
private theorem range54From20489To2673 : Segment 54 20489 20736 2574 2673 :=
  paid (pc:=75) (v:=248415661806) (by decide) source079_valid tests54_079_2574 fee54_079_20736 (by decide +kernel)

private theorem tests54_070_2673 : ∀ z∈source070.plan.table,z.1.Valid 54 2673 := by decide +kernel
private theorem fee54_070_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source070.plan.table+
      4*20736*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*192694176627 := by decide +kernel
private theorem range54From20489To2687 : Segment 54 20489 20736 2673 2687 :=
  paid (pc:=75) (v:=192694176627) (by decide) source070_valid tests54_070_2673 fee54_070_20736 (by decide +kernel)

private theorem tests54_073_2687 : ∀ z∈source073.plan.table,z.1.Valid 54 2687 := by decide +kernel
private theorem fee54_073_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source073.plan.table+
      4*20736*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*286843760256 := by decide +kernel
private theorem range54From20489To2855 : Segment 54 20489 20736 2687 2855 :=
  paid (pc:=73) (v:=286843760256) (by decide) source073_valid tests54_073_2687 fee54_073_20736 (by decide +kernel)

private theorem tests54_080_2855 : ∀ z∈source080.plan.table,z.1.Valid 54 2855 := by decide +kernel
private theorem fee54_080_20736 :
    PopulationFees20258.bill (n:=20736) (PopulationFees20258.tabulate (20736-1) 256) source080.plan.table+
      4*20736*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*209216056270 := by decide +kernel
private theorem range54From20489To2863 : Segment 54 20489 20736 2855 2863 :=
  paid (pc:=73) (v:=209216056270) (by decide) source080_valid tests54_080_2855 fee54_080_20736 (by decide +kernel)

private theorem range54From20489 : Win 54 20489 20736 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From20489To2380 range54From20489To2452) (join_population range54From20489To2506 range54From20489To2574)) (join_population (join_population range54From20489To2673 range54From20489To2687) (join_population range54From20489To2855 range54From20489To2863)))

private theorem fee54_074_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source074.plan.table+
      4*21008*NaturalPopulation20258.weights source074.extras≤source074.plan.scale*138614162967 := by decide +kernel
private theorem range54From20737To2392 : Segment 54 20737 21008 0 2392 :=
  paid (pc:=77) (v:=138614162967) (by decide) source074_valid tests54_074_0 fee54_074_21008 (by decide +kernel)

private theorem tests54_075_2392 : ∀ z∈source075.plan.table,z.1.Valid 54 2392 := by decide +kernel
private theorem fee54_075_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source075.plan.table+
      4*21008*NaturalPopulation20258.weights source075.extras≤source075.plan.scale*178441705916 := by decide +kernel
private theorem range54From20737To2460 : Segment 54 20737 21008 2392 2460 :=
  paid (pc:=77) (v:=178441705916) (by decide) source075_valid tests54_075_2392 fee54_075_21008 (by decide +kernel)

private theorem tests54_076_2460 : ∀ z∈source076.plan.table,z.1.Valid 54 2460 := by decide +kernel
private theorem fee54_076_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source076.plan.table+
      4*21008*NaturalPopulation20258.weights source076.extras≤source076.plan.scale*221860457023 := by decide +kernel
private theorem range54From20737To2510 : Segment 54 20737 21008 2460 2510 :=
  paid (pc:=76) (v:=221860457023) (by decide) source076_valid tests54_076_2460 fee54_076_21008 (by decide +kernel)

private theorem tests54_077_2510 : ∀ z∈source077.plan.table,z.1.Valid 54 2510 := by decide +kernel
private theorem fee54_077_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source077.plan.table+
      4*21008*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*212320750160 := by decide +kernel
private theorem range54From20737To2576 : Segment 54 20737 21008 2510 2576 :=
  paid (pc:=76) (v:=212320750160) (by decide) source077_valid tests54_077_2510 fee54_077_21008 (by decide +kernel)

private theorem tests54_079_2576 : ∀ z∈source079.plan.table,z.1.Valid 54 2576 := by decide +kernel
private theorem fee54_079_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source079.plan.table+
      4*21008*NaturalPopulation20258.weights source079.extras≤source079.plan.scale*254254482076 := by decide +kernel
private theorem range54From20737To2668 : Segment 54 20737 21008 2576 2668 :=
  paid (pc:=75) (v:=254254482076) (by decide) source079_valid tests54_079_2576 fee54_079_21008 (by decide +kernel)

private theorem tests54_070_2668 : ∀ z∈source070.plan.table,z.1.Valid 54 2668 := by decide +kernel
private theorem fee54_070_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source070.plan.table+
      4*21008*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*197265562660 := by decide +kernel
private theorem range54From20737To2686 : Segment 54 20737 21008 2668 2686 :=
  paid (pc:=75) (v:=197265562660) (by decide) source070_valid tests54_070_2668 fee54_070_21008 (by decide +kernel)

private theorem fee54_073_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source073.plan.table+
      4*21008*NaturalPopulation20258.weights source073.extras≤source073.plan.scale*293557084664 := by decide +kernel
private theorem range54From20737To2834 : Segment 54 20737 21008 2686 2834 :=
  paid (pc:=74) (v:=293557084664) (by decide) source073_valid tests54_073_2686 fee54_073_21008 (by decide +kernel)

private theorem tests54_080_2834 : ∀ z∈source080.plan.table,z.1.Valid 54 2834 := by decide +kernel
private theorem fee54_080_21008 :
    PopulationFees20258.bill (n:=21008) (PopulationFees20258.tabulate (21008-1) 256) source080.plan.table+
      4*21008*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*214188972156 := by decide +kernel
private theorem range54From20737To2863 : Segment 54 20737 21008 2834 2863 :=
  paid (pc:=73) (v:=214188972156) (by decide) source080_valid tests54_080_2834 fee54_080_21008 (by decide +kernel)

private theorem range54From20737 : Win 54 20737 21008 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range54From20737To2392 range54From20737To2460) (join_population range54From20737To2510 range54From20737To2576)) (join_population (join_population range54From20737To2668 range54From20737To2686) (join_population range54From20737To2834 range54From20737To2863)))

theorem cut54From20258 : Win 54 20258 21008 :=
  (join_ground range54From20258 (join_ground range54From20489 range54From20737))

end JSP233.FiniteCutRanges20258
