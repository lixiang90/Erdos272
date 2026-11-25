module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source095
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_22637 :
    PopulationFees20258.bill (n:=22637) (PopulationFees20258.tabulate (22637-1) 256) source093.plan.table+
      4*22637*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*176407489533 := by decide +kernel
private theorem range57From22201To2621 : Segment 57 22201 22637 0 2621 :=
  paid (pc:=76) (v:=176407489533) (by decide) source093_valid tests57_093_0 fee57_093_22637 (by decide +kernel)

private theorem tests57_095_2621 : ∀ z∈source095.plan.table,z.1.Valid 57 2621 := by decide +kernel
private theorem fee57_095_22637 :
    PopulationFees20258.bill (n:=22637) (PopulationFees20258.tabulate (22637-1) 256) source095.plan.table+
      4*22637*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*272318557043 := by decide +kernel
private theorem range57From22201To2766 : Segment 57 22201 22637 2621 2766 :=
  paid (pc:=75) (v:=272318557043) (by decide) source095_valid tests57_095_2621 fee57_095_22637 (by decide +kernel)

private theorem tests57_094_2766 : ∀ z∈source094.plan.table,z.1.Valid 57 2766 := by decide +kernel
private theorem fee57_094_22637 :
    PopulationFees20258.bill (n:=22637) (PopulationFees20258.tabulate (22637-1) 256) source094.plan.table+
      4*22637*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*264459749681 := by decide +kernel
private theorem range57From22201To2821 : Segment 57 22201 22637 2766 2821 :=
  paid (pc:=75) (v:=264459749681) (by decide) source094_valid tests57_094_2766 fee57_094_22637 (by decide +kernel)

private theorem tests57_094_2821 : ∀ z∈source094.plan.table,z.1.Valid 57 2821 := by decide +kernel
private theorem range57From22201To2823 : Segment 57 22201 22637 2821 2823 :=
  paid (pc:=75) (v:=264459749681) (by decide) source094_valid tests57_094_2821 fee57_094_22637 (by decide +kernel)

private theorem tests57_092_2823 : ∀ z∈source092.plan.table,z.1.Valid 57 2823 := by decide +kernel
private theorem fee57_092_22637 :
    PopulationFees20258.bill (n:=22637) (PopulationFees20258.tabulate (22637-1) 256) source092.plan.table+
      4*22637*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*249141072833 := by decide +kernel
private theorem range57From22201To2923 : Segment 57 22201 22637 2823 2923 :=
  paid (pc:=74) (v:=249141072833) (by decide) source092_valid tests57_092_2823 fee57_092_22637 (by decide +kernel)

private theorem tests57_097_2923 : ∀ z∈source097.plan.table,z.1.Valid 57 2923 := by decide +kernel
private theorem fee57_097_22637 :
    PopulationFees20258.bill (n:=22637) (PopulationFees20258.tabulate (22637-1) 256) source097.plan.table+
      4*22637*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*277141822749 := by decide +kernel
private theorem range57From22201To3193 : Segment 57 22201 22637 2923 3193 :=
  paid (pc:=71) (v:=277141822749) (by decide) source097_valid tests57_097_2923 fee57_097_22637 (by decide +kernel)

private theorem range57From22201 : Win 57 22201 22637 :=
  complete (by decide) (by decide) (join_population (join_population range57From22201To2621 (join_population range57From22201To2766 range57From22201To2821)) (join_population range57From22201To2823 (join_population range57From22201To2923 range57From22201To3193)))

private theorem fee57_093_23116 :
    PopulationFees20258.bill (n:=23116) (PopulationFees20258.tabulate (23116-1) 256) source093.plan.table+
      4*23116*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*183463443381 := by decide +kernel
private theorem range57From22638To2637 : Segment 57 22638 23116 0 2637 :=
  paid (pc:=76) (v:=183463443381) (by decide) source093_valid tests57_093_0 fee57_093_23116 (by decide +kernel)

private theorem tests57_095_2637 : ∀ z∈source095.plan.table,z.1.Valid 57 2637 := by decide +kernel
private theorem fee57_095_23116 :
    PopulationFees20258.bill (n:=23116) (PopulationFees20258.tabulate (23116-1) 256) source095.plan.table+
      4*23116*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*283042618313 := by decide +kernel
private theorem range57From22638To2770 : Segment 57 22638 23116 2637 2770 :=
  paid (pc:=75) (v:=283042618313) (by decide) source095_valid tests57_095_2637 fee57_095_23116 (by decide +kernel)

private theorem tests57_094_2770 : ∀ z∈source094.plan.table,z.1.Valid 57 2770 := by decide +kernel
private theorem fee57_094_23116 :
    PopulationFees20258.bill (n:=23116) (PopulationFees20258.tabulate (23116-1) 256) source094.plan.table+
      4*23116*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*274882103989 := by decide +kernel
private theorem range57From22638To2821 : Segment 57 22638 23116 2770 2821 :=
  paid (pc:=75) (v:=274882103989) (by decide) source094_valid tests57_094_2770 fee57_094_23116 (by decide +kernel)

private theorem range57From22638To2823 : Segment 57 22638 23116 2821 2823 :=
  paid (pc:=75) (v:=274882103989) (by decide) source094_valid tests57_094_2821 fee57_094_23116 (by decide +kernel)

private theorem fee57_092_23116 :
    PopulationFees20258.bill (n:=23116) (PopulationFees20258.tabulate (23116-1) 256) source092.plan.table+
      4*23116*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*258950734896 := by decide +kernel
private theorem range57From22638To2919 : Segment 57 22638 23116 2823 2919 :=
  paid (pc:=74) (v:=258950734896) (by decide) source092_valid tests57_092_2823 fee57_092_23116 (by decide +kernel)

private theorem tests57_097_2919 : ∀ z∈source097.plan.table,z.1.Valid 57 2919 := by decide +kernel
private theorem fee57_097_23116 :
    PopulationFees20258.bill (n:=23116) (PopulationFees20258.tabulate (23116-1) 256) source097.plan.table+
      4*23116*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*288081808678 := by decide +kernel
private theorem range57From22638To3193 : Segment 57 22638 23116 2919 3193 :=
  paid (pc:=72) (v:=288081808678) (by decide) source097_valid tests57_097_2919 fee57_097_23116 (by decide +kernel)

private theorem range57From22638 : Win 57 22638 23116 :=
  complete (by decide) (by decide) (join_population (join_population range57From22638To2637 (join_population range57From22638To2770 range57From22638To2821)) (join_population range57From22638To2823 (join_population range57From22638To2919 range57From22638To3193)))

private theorem fee57_093_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source093.plan.table+
      4*23652*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*191275500640 := by decide +kernel
private theorem range57From23117To2654 : Segment 57 23117 23652 0 2654 :=
  paid (pc:=76) (v:=191275500640) (by decide) source093_valid tests57_093_0 fee57_093_23652 (by decide +kernel)

private theorem tests57_095_2654 : ∀ z∈source095.plan.table,z.1.Valid 57 2654 := by decide +kernel
private theorem fee57_095_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source095.plan.table+
      4*23652*NaturalPopulation20258.weights source095.extras≤source095.plan.scale*294938718193 := by decide +kernel
private theorem range57From23117To2773 : Segment 57 23117 23652 2654 2773 :=
  paid (pc:=75) (v:=294938718193) (by decide) source095_valid tests57_095_2654 fee57_095_23652 (by decide +kernel)

private theorem tests57_094_2773 : ∀ z∈source094.plan.table,z.1.Valid 57 2773 := by decide +kernel
private theorem fee57_094_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source094.plan.table+
      4*23652*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*286450061371 := by decide +kernel
private theorem range57From23117To2822 : Segment 57 23117 23652 2773 2822 :=
  paid (pc:=75) (v:=286450061371) (by decide) source094_valid tests57_094_2773 fee57_094_23652 (by decide +kernel)

private theorem tests57_094_2822 : ∀ z∈source094.plan.table,z.1.Valid 57 2822 := by decide +kernel
private theorem range57From23117To2824 : Segment 57 23117 23652 2822 2824 :=
  paid (pc:=75) (v:=286450061371) (by decide) source094_valid tests57_094_2822 fee57_094_23652 (by decide +kernel)

private theorem tests57_092_2824 : ∀ z∈source092.plan.table,z.1.Valid 57 2824 := by decide +kernel
private theorem fee57_092_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source092.plan.table+
      4*23652*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*269961133419 := by decide +kernel
private theorem range57From23117To2915 : Segment 57 23117 23652 2824 2915 :=
  paid (pc:=74) (v:=269961133419) (by decide) source092_valid tests57_092_2824 fee57_092_23652 (by decide +kernel)

private theorem tests57_097_2915 : ∀ z∈source097.plan.table,z.1.Valid 57 2915 := by decide +kernel
private theorem fee57_097_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source097.plan.table+
      4*23652*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*300219854643 := by decide +kernel
private theorem range57From23117To3168 : Segment 57 23117 23652 2915 3168 :=
  paid (pc:=72) (v:=300219854643) (by decide) source097_valid tests57_097_2915 fee57_097_23652 (by decide +kernel)

private theorem tests57_096_3168 : ∀ z∈source096.plan.table,z.1.Valid 57 3168 := by decide +kernel
private theorem fee57_096_23652 :
    PopulationFees20258.bill (n:=23652) (PopulationFees20258.tabulate (23652-1) 256) source096.plan.table+
      4*23652*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*279039684862 := by decide +kernel
private theorem range57From23117To3193 : Segment 57 23117 23652 3168 3193 :=
  paid (pc:=72) (v:=279039684862) (by decide) source096_valid tests57_096_3168 fee57_096_23652 (by decide +kernel)

private theorem range57From23117 : Win 57 23117 23652 :=
  complete (by decide) (by decide) (join_population (join_population range57From23117To2654 (join_population range57From23117To2773 range57From23117To2822)) (join_population (join_population range57From23117To2824 range57From23117To2915) (join_population range57From23117To3168 range57From23117To3193)))

theorem cut57From22201 : Win 57 22201 23652 :=
  (join_ground range57From22201 (join_ground range57From22638 range57From23117))

end JSP233.FiniteCutRanges20258
