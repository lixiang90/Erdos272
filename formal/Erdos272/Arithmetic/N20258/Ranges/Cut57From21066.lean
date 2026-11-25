module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source091
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source093.plan.table+
      4*21419*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*159371650100 := by decide +kernel
private theorem range57From21066To2575 : Segment 57 21066 21419 0 2575 :=
  paid (pc:=76) (v:=159371650100) (by decide) source093_valid tests57_093_0 fee57_093_21419 (by decide +kernel)

private theorem tests57_093_2575 : ∀ z∈source093.plan.table,z.1.Valid 57 2575 := by decide +kernel
private theorem range57From21066To2591 : Segment 57 21066 21419 2575 2591 :=
  paid (pc:=76) (v:=159371650100) (by decide) source093_valid tests57_093_2575 fee57_093_21419 (by decide +kernel)

private theorem tests57_093_2591 : ∀ z∈source093.plan.table,z.1.Valid 57 2591 := by decide +kernel
private theorem range57From21066To2593 : Segment 57 21066 21419 2591 2593 :=
  paid (pc:=76) (v:=159371650100) (by decide) source093_valid tests57_093_2591 fee57_093_21419 (by decide +kernel)

private theorem tests57_091_2593 : ∀ z∈source091.plan.table,z.1.Valid 57 2593 := by decide +kernel
private theorem fee57_091_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source091.plan.table+
      4*21419*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*261206482665 := by decide +kernel
private theorem range57From21066To2645 : Segment 57 21066 21419 2593 2645 :=
  paid (pc:=75) (v:=261206482665) (by decide) source091_valid tests57_091_2593 fee57_091_21419 (by decide +kernel)

private theorem tests57_095_2645 : ∀ z∈source095.plan.table,z.1.Valid 57 2645 := by decide +kernel
private theorem fee57_095_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source095.plan.table+
      4*21419*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*246375643752 := by decide +kernel
private theorem range57From21066To2762 : Segment 57 21066 21419 2645 2762 :=
  paid (pc:=74) (v:=246375643752) (by decide) source095_valid tests57_095_2645 fee57_095_21419 (by decide +kernel)

private theorem tests57_094_2762 : ∀ z∈source094.plan.table,z.1.Valid 57 2762 := by decide +kernel
private theorem fee57_094_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source094.plan.table+
      4*21419*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*239248383398 := by decide +kernel
private theorem range57From21066To2823 : Segment 57 21066 21419 2762 2823 :=
  paid (pc:=74) (v:=239248383398) (by decide) source094_valid tests57_094_2762 fee57_094_21419 (by decide +kernel)

private theorem tests57_092_2823 : ∀ z∈source092.plan.table,z.1.Valid 57 2823 := by decide +kernel
private theorem fee57_092_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source092.plan.table+
      4*21419*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*225218450573 := by decide +kernel
private theorem range57From21066To2941 : Segment 57 21066 21419 2823 2941 :=
  paid (pc:=73) (v:=225218450573) (by decide) source092_valid tests57_092_2823 fee57_092_21419 (by decide +kernel)

private theorem tests57_097_2941 : ∀ z∈source097.plan.table,z.1.Valid 57 2941 := by decide +kernel
private theorem fee57_097_21419 :
    PopulationFees20258.bill (n:=21419) (PopulationFees20258.tabulate (21419-1) 256) source097.plan.table+
      4*21419*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*250676759519 := by decide +kernel
private theorem range57From21066To3193 : Segment 57 21066 21419 2941 3193 :=
  paid (pc:=70) (v:=250676759519) (by decide) source097_valid tests57_097_2941 fee57_097_21419 (by decide +kernel)

private theorem range57From21066 : Win 57 21066 21419 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range57From21066To2575 range57From21066To2591) (join_population range57From21066To2593 range57From21066To2645)) (join_population (join_population range57From21066To2762 range57From21066To2823) (join_population range57From21066To2941 range57From21066To3193)))

private theorem fee57_093_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source093.plan.table+
      4*21796*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*164521576019 := by decide +kernel
private theorem range57From21420To2589 : Segment 57 21420 21796 0 2589 :=
  paid (pc:=76) (v:=164521576019) (by decide) source093_valid tests57_093_0 fee57_093_21796 (by decide +kernel)

private theorem tests57_093_2589 : ∀ z∈source093.plan.table,z.1.Valid 57 2589 := by decide +kernel
private theorem range57From21420To2606 : Segment 57 21420 21796 2589 2606 :=
  paid (pc:=76) (v:=164521576019) (by decide) source093_valid tests57_093_2589 fee57_093_21796 (by decide +kernel)

private theorem tests57_091_2606 : ∀ z∈source091.plan.table,z.1.Valid 57 2606 := by decide +kernel
private theorem fee57_091_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source091.plan.table+
      4*21796*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*269547589056 := by decide +kernel
private theorem range57From21420To2650 : Segment 57 21420 21796 2606 2650 :=
  paid (pc:=75) (v:=269547589056) (by decide) source091_valid tests57_091_2606 fee57_091_21796 (by decide +kernel)

private theorem tests57_095_2650 : ∀ z∈source095.plan.table,z.1.Valid 57 2650 := by decide +kernel
private theorem fee57_095_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source095.plan.table+
      4*21796*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*254237700221 := by decide +kernel
private theorem range57From21420To2763 : Segment 57 21420 21796 2650 2763 :=
  paid (pc:=74) (v:=254237700221) (by decide) source095_valid tests57_095_2650 fee57_095_21796 (by decide +kernel)

private theorem tests57_094_2763 : ∀ z∈source094.plan.table,z.1.Valid 57 2763 := by decide +kernel
private theorem fee57_094_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source094.plan.table+
      4*21796*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*246870504724 := by decide +kernel
private theorem range57From21420To2821 : Segment 57 21420 21796 2763 2821 :=
  paid (pc:=74) (v:=246870504724) (by decide) source094_valid tests57_094_2763 fee57_094_21796 (by decide +kernel)

private theorem tests57_094_2821 : ∀ z∈source094.plan.table,z.1.Valid 57 2821 := by decide +kernel
private theorem range57From21420To2823 : Segment 57 21420 21796 2821 2823 :=
  paid (pc:=74) (v:=246870504724) (by decide) source094_valid tests57_094_2821 fee57_094_21796 (by decide +kernel)

private theorem fee57_092_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source092.plan.table+
      4*21796*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*232463099882 := by decide +kernel
private theorem range57From21420To2933 : Segment 57 21420 21796 2823 2933 :=
  paid (pc:=73) (v:=232463099882) (by decide) source092_valid tests57_092_2823 fee57_092_21796 (by decide +kernel)

private theorem tests57_097_2933 : ∀ z∈source097.plan.table,z.1.Valid 57 2933 := by decide +kernel
private theorem fee57_097_21796 :
    PopulationFees20258.bill (n:=21796) (PopulationFees20258.tabulate (21796-1) 256) source097.plan.table+
      4*21796*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*258686154608 := by decide +kernel
private theorem range57From21420To3193 : Segment 57 21420 21796 2933 3193 :=
  paid (pc:=70) (v:=258686154608) (by decide) source097_valid tests57_097_2933 fee57_097_21796 (by decide +kernel)

private theorem range57From21420 : Win 57 21420 21796 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range57From21420To2589 range57From21420To2606) (join_population range57From21420To2650 range57From21420To2763)) (join_population (join_population range57From21420To2821 range57From21420To2823) (join_population range57From21420To2933 range57From21420To3193)))

private theorem fee57_093_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source093.plan.table+
      4*22200*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*170185652667 := by decide +kernel
private theorem range57From21797To2606 : Segment 57 21797 22200 0 2606 :=
  paid (pc:=76) (v:=170185652667) (by decide) source093_valid tests57_093_0 fee57_093_22200 (by decide +kernel)

private theorem fee57_091_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source091.plan.table+
      4*22200*NaturalPopulation20258.weights source091.extras≤source091.plan.scale*278726541986 := by decide +kernel
private theorem range57From21797To2656 : Segment 57 21797 22200 2606 2656 :=
  paid (pc:=76) (v:=278726541986) (by decide) source091_valid tests57_091_2606 fee57_091_22200 (by decide +kernel)

private theorem tests57_095_2656 : ∀ z∈source095.plan.table,z.1.Valid 57 2656 := by decide +kernel
private theorem fee57_095_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source095.plan.table+
      4*22200*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*262864221766 := by decide +kernel
private theorem range57From21797To2765 : Segment 57 21797 22200 2656 2765 :=
  paid (pc:=75) (v:=262864221766) (by decide) source095_valid tests57_095_2656 fee57_095_22200 (by decide +kernel)

private theorem tests57_094_2765 : ∀ z∈source094.plan.table,z.1.Valid 57 2765 := by decide +kernel
private theorem fee57_094_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source094.plan.table+
      4*22200*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*255265239183 := by decide +kernel
private theorem range57From21797To2821 : Segment 57 21797 22200 2765 2821 :=
  paid (pc:=74) (v:=255265239183) (by decide) source094_valid tests57_094_2765 fee57_094_22200 (by decide +kernel)

private theorem range57From21797To2823 : Segment 57 21797 22200 2821 2823 :=
  paid (pc:=74) (v:=255265239183) (by decide) source094_valid tests57_094_2821 fee57_094_22200 (by decide +kernel)

private theorem fee57_092_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source092.plan.table+
      4*22200*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*240445146494 := by decide +kernel
private theorem range57From21797To2927 : Segment 57 21797 22200 2823 2927 :=
  paid (pc:=73) (v:=240445146494) (by decide) source092_valid tests57_092_2823 fee57_092_22200 (by decide +kernel)

private theorem tests57_097_2927 : ∀ z∈source097.plan.table,z.1.Valid 57 2927 := by decide +kernel
private theorem fee57_097_22200 :
    PopulationFees20258.bill (n:=22200) (PopulationFees20258.tabulate (22200-1) 256) source097.plan.table+
      4*22200*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*267491867549 := by decide +kernel
private theorem range57From21797To3193 : Segment 57 21797 22200 2927 3193 :=
  paid (pc:=71) (v:=267491867549) (by decide) source097_valid tests57_097_2927 fee57_097_22200 (by decide +kernel)

private theorem range57From21797 : Win 57 21797 22200 :=
  complete (by decide) (by decide) (join_population (join_population range57From21797To2606 (join_population range57From21797To2656 range57From21797To2765)) (join_population (join_population range57From21797To2821 range57From21797To2823) (join_population range57From21797To2927 range57From21797To3193)))

theorem cut57From21066 : Win 57 21066 22200 :=
  (join_ground range57From21066 (join_ground range57From21420 range57From21797))

end JSP233.FiniteCutRanges20258
