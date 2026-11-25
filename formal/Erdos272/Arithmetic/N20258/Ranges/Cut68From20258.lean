module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source119
public import Erdos272.Arithmetic.N20258.Sources.Source120

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests68_120_0 : ∀ z∈source120.plan.table,z.1.Valid 68 0 := by decide +kernel
private theorem fee68_120_24042 :
    PopulationFees20258.bill (n:=24042) (PopulationFees20258.tabulate (24042-1) 256) source120.plan.table+
      4*24042*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*269695083188 := by decide +kernel
private theorem range68From20258To2575 : Segment 68 20258 24042 0 2575 :=
  paid (pc:=58) (v:=269695083188) (by decide) source120_valid tests68_120_0 fee68_120_24042 (by decide +kernel)

private theorem tests68_120_2575 : ∀ z∈source120.plan.table,z.1.Valid 68 2575 := by decide +kernel
private theorem range68From20258To2756 : Segment 68 20258 24042 2575 2756 :=
  paid (pc:=56) (v:=269695083188) (by decide) source120_valid tests68_120_2575 fee68_120_24042 (by decide +kernel)

private theorem tests68_120_2756 : ∀ z∈source120.plan.table,z.1.Valid 68 2756 := by decide +kernel
private theorem range68From20258To2843 : Segment 68 20258 24042 2756 2843 :=
  paid (pc:=55) (v:=269695083188) (by decide) source120_valid tests68_120_2756 fee68_120_24042 (by decide +kernel)

private theorem tests68_120_2843 : ∀ z∈source120.plan.table,z.1.Valid 68 2843 := by decide +kernel
private theorem range68From20258To4557 : Segment 68 20258 24042 2843 4557 :=
  paid (pc:=54) (v:=269695083188) (by decide) source120_valid tests68_120_2843 fee68_120_24042 (by decide +kernel)

private theorem range68From20258 : Win 68 20258 24042 :=
  complete (by decide) (by decide) (join_population (join_population range68From20258To2575 range68From20258To2756) (join_population range68From20258To2843 range68From20258To4557))

private theorem fee68_120_26376 :
    PopulationFees20258.bill (n:=26376) (PopulationFees20258.tabulate (26376-1) 256) source120.plan.table+
      4*26376*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*319143631018 := by decide +kernel
private theorem range68From24043To3610 : Segment 68 24043 26376 0 3610 :=
  paid (pc:=62) (v:=319143631018) (by decide) source120_valid tests68_120_0 fee68_120_26376 (by decide +kernel)

private theorem tests68_120_3610 : ∀ z∈source120.plan.table,z.1.Valid 68 3610 := by decide +kernel
private theorem range68From24043To3687 : Segment 68 24043 26376 3610 3687 :=
  paid (pc:=61) (v:=319143631018) (by decide) source120_valid tests68_120_3610 fee68_120_26376 (by decide +kernel)

private theorem tests68_120_3687 : ∀ z∈source120.plan.table,z.1.Valid 68 3687 := by decide +kernel
private theorem range68From24043To3694 : Segment 68 24043 26376 3687 3694 :=
  paid (pc:=61) (v:=319143631018) (by decide) source120_valid tests68_120_3687 fee68_120_26376 (by decide +kernel)

private theorem tests68_119_3694 : ∀ z∈source119.plan.table,z.1.Valid 68 3694 := by decide +kernel
private theorem fee68_119_26376 :
    PopulationFees20258.bill (n:=26376) (PopulationFees20258.tabulate (26376-1) 256) source119.plan.table+
      4*26376*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*769253854870 := by decide +kernel
private theorem range68From24043To4557 : Segment 68 24043 26376 3694 4557 :=
  paid (pc:=72) (v:=769253854870) (by decide) source119_valid tests68_119_3694 fee68_119_26376 (by decide +kernel)

private theorem range68From24043 : Win 68 24043 26376 :=
  complete (by decide) (by decide) (join_population (join_population range68From24043To3610 range68From24043To3687) (join_population range68From24043To3694 range68From24043To4557))

private theorem fee68_120_28432 :
    PopulationFees20258.bill (n:=28432) (PopulationFees20258.tabulate (28432-1) 256) source120.plan.table+
      4*28432*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*366103127260 := by decide +kernel
private theorem range68From26377To3647 : Segment 68 26377 28432 0 3647 :=
  paid (pc:=66) (v:=366103127260) (by decide) source120_valid tests68_120_0 fee68_120_28432 (by decide +kernel)

private theorem tests68_120_3647 : ∀ z∈source120.plan.table,z.1.Valid 68 3647 := by decide +kernel
private theorem range68From26377To3691 : Segment 68 26377 28432 3647 3691 :=
  paid (pc:=66) (v:=366103127260) (by decide) source120_valid tests68_120_3647 fee68_120_28432 (by decide +kernel)

private theorem tests68_120_3691 : ∀ z∈source120.plan.table,z.1.Valid 68 3691 := by decide +kernel
private theorem range68From26377To3693 : Segment 68 26377 28432 3691 3693 :=
  paid (pc:=66) (v:=366103127260) (by decide) source120_valid tests68_120_3691 fee68_120_28432 (by decide +kernel)

private theorem tests68_119_3693 : ∀ z∈source119.plan.table,z.1.Valid 68 3693 := by decide +kernel
private theorem fee68_119_28432 :
    PopulationFees20258.bill (n:=28432) (PopulationFees20258.tabulate (28432-1) 256) source119.plan.table+
      4*28432*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*878642862433 := by decide +kernel
private theorem range68From26377To4557 : Segment 68 26377 28432 3693 4557 :=
  paid (pc:=66) (v:=878642862433) (by decide) source119_valid tests68_119_3693 fee68_119_28432 (by decide +kernel)

private theorem range68From26377 : Win 68 26377 28432 :=
  complete (by decide) (by decide) (join_population (join_population range68From26377To3647 range68From26377To3691) (join_population range68From26377To3693 range68From26377To4557))

private theorem fee68_120_30504 :
    PopulationFees20258.bill (n:=30504) (PopulationFees20258.tabulate (30504-1) 256) source120.plan.table+
      4*30504*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*416630788072 := by decide +kernel
private theorem range68From28433To3660 : Segment 68 28433 30504 0 3660 :=
  paid (pc:=68) (v:=416630788072) (by decide) source120_valid tests68_120_0 fee68_120_30504 (by decide +kernel)

private theorem tests68_120_3660 : ∀ z∈source120.plan.table,z.1.Valid 68 3660 := by decide +kernel
private theorem range68From28433To3691 : Segment 68 28433 30504 3660 3691 :=
  paid (pc:=68) (v:=416630788072) (by decide) source120_valid tests68_120_3660 fee68_120_30504 (by decide +kernel)

private theorem range68From28433To3693 : Segment 68 28433 30504 3691 3693 :=
  paid (pc:=68) (v:=416630788072) (by decide) source120_valid tests68_120_3691 fee68_120_30504 (by decide +kernel)

private theorem fee68_119_30504 :
    PopulationFees20258.bill (n:=30504) (PopulationFees20258.tabulate (30504-1) 256) source119.plan.table+
      4*30504*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*996137411509 := by decide +kernel
private theorem range68From28433To4557 : Segment 68 28433 30504 3693 4557 :=
  paid (pc:=62) (v:=996137411509) (by decide) source119_valid tests68_119_3693 fee68_119_30504 (by decide +kernel)

private theorem range68From28433 : Win 68 28433 30504 :=
  complete (by decide) (by decide) (join_population (join_population range68From28433To3660 range68From28433To3691) (join_population range68From28433To3693 range68From28433To4557))

private theorem fee68_120_32600 :
    PopulationFees20258.bill (n:=32600) (PopulationFees20258.tabulate (32600-1) 256) source120.plan.table+
      4*32600*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*470733934488 := by decide +kernel
private theorem range68From30505To3737 : Segment 68 30505 32600 0 3737 :=
  paid (pc:=70) (v:=470733934488) (by decide) source120_valid tests68_120_0 fee68_120_32600 (by decide +kernel)

private theorem tests68_119_3737 : ∀ z∈source119.plan.table,z.1.Valid 68 3737 := by decide +kernel
private theorem fee68_119_32600 :
    PopulationFees20258.bill (n:=32600) (PopulationFees20258.tabulate (32600-1) 256) source119.plan.table+
      4*32600*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1121969214758 := by decide +kernel
private theorem range68From30505To4479 : Segment 68 30505 32600 3737 4479 :=
  paid (pc:=65) (v:=1121969214758) (by decide) source119_valid tests68_119_3737 fee68_119_32600 (by decide +kernel)

private theorem tests68_119_4479 : ∀ z∈source119.plan.table,z.1.Valid 68 4479 := by decide +kernel
private theorem range68From30505To4550 : Segment 68 30505 32600 4479 4550 :=
  paid (pc:=65) (v:=1121969214758) (by decide) source119_valid tests68_119_4479 fee68_119_32600 (by decide +kernel)

private theorem tests68_119_4550 : ∀ z∈source119.plan.table,z.1.Valid 68 4550 := by decide +kernel
private theorem range68From30505To4557 : Segment 68 30505 32600 4550 4557 :=
  paid (pc:=65) (v:=1121969214758) (by decide) source119_valid tests68_119_4550 fee68_119_32600 (by decide +kernel)

private theorem range68From30505 : Win 68 30505 32600 :=
  complete (by decide) (by decide) (join_population (join_population range68From30505To3737 range68From30505To4479) (join_population range68From30505To4550 range68From30505To4557))

private theorem fee68_120_34414 :
    PopulationFees20258.bill (n:=34414) (PopulationFees20258.tabulate (34414-1) 256) source120.plan.table+
      4*34414*NaturalPopulation20258.weights source120.extras≤source120.plan.scale*520675518685 := by decide +kernel
private theorem range68From32601To3965 : Segment 68 32601 34414 0 3965 :=
  paid (pc:=71) (v:=520675518685) (by decide) source120_valid tests68_120_0 fee68_120_34414 (by decide +kernel)

private theorem tests68_119_3965 : ∀ z∈source119.plan.table,z.1.Valid 68 3965 := by decide +kernel
private theorem fee68_119_34414 :
    PopulationFees20258.bill (n:=34414) (PopulationFees20258.tabulate (34414-1) 256) source119.plan.table+
      4*34414*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1237215835094 := by decide +kernel
private theorem range68From32601To4528 : Segment 68 32601 34414 3965 4528 :=
  paid (pc:=68) (v:=1237215835094) (by decide) source119_valid tests68_119_3965 fee68_119_34414 (by decide +kernel)

private theorem tests68_119_4528 : ∀ z∈source119.plan.table,z.1.Valid 68 4528 := by decide +kernel
private theorem range68From32601To4557 : Segment 68 32601 34414 4528 4557 :=
  paid (pc:=68) (v:=1237215835094) (by decide) source119_valid tests68_119_4528 fee68_119_34414 (by decide +kernel)

private theorem range68From32601 : Win 68 32601 34414 :=
  complete (by decide) (by decide) (join_population range68From32601To3965 (join_population range68From32601To4528 range68From32601To4557))

theorem cut68From20258 : Win 68 20258 34414 :=
  (join_ground (join_ground range68From20258 (join_ground range68From24043 range68From26377)) (join_ground range68From28433 (join_ground range68From30505 range68From32601)))

end JSP233.FiniteCutRanges20258
