module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_30493 :
    PopulationFees20258.bill (n:=30493) (PopulationFees20258.tabulate (30493-1) 256) source093.plan.table+
      4*30493*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*306967732339 := by decide +kernel
private theorem range57From29020To2857 : Segment 57 29020 30493 0 2857 :=
  paid (pc:=76) (v:=306967732339) (by decide) source093_valid tests57_093_0 fee57_093_30493 (by decide +kernel)

private theorem tests57_092_2857 : ∀ z∈source092.plan.table,z.1.Valid 57 2857 := by decide +kernel
private theorem fee57_092_30493 :
    PopulationFees20258.bill (n:=30493) (PopulationFees20258.tabulate (30493-1) 256) source092.plan.table+
      4*30493*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*431810323658 := by decide +kernel
private theorem range57From29020To2979 : Segment 57 29020 30493 2857 2979 :=
  paid (pc:=75) (v:=431810323658) (by decide) source092_valid tests57_092_2857 fee57_092_30493 (by decide +kernel)

private theorem tests57_097_2979 : ∀ z∈source097.plan.table,z.1.Valid 57 2979 := by decide +kernel
private theorem fee57_097_30493 :
    PopulationFees20258.bill (n:=30493) (PopulationFees20258.tabulate (30493-1) 256) source097.plan.table+
      4*30493*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*479430761312 := by decide +kernel
private theorem range57From29020To3096 : Segment 57 29020 30493 2979 3096 :=
  paid (pc:=75) (v:=479430761312) (by decide) source097_valid tests57_097_2979 fee57_097_30493 (by decide +kernel)

private theorem tests57_096_3096 : ∀ z∈source096.plan.table,z.1.Valid 57 3096 := by decide +kernel
private theorem fee57_096_30493 :
    PopulationFees20258.bill (n:=30493) (PopulationFees20258.tabulate (30493-1) 256) source096.plan.table+
      4*30493*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*446389754948 := by decide +kernel
private theorem range57From29020To3191 : Segment 57 29020 30493 3096 3191 :=
  paid (pc:=74) (v:=446389754948) (by decide) source096_valid tests57_096_3096 fee57_096_30493 (by decide +kernel)

private theorem tests57_096_3191 : ∀ z∈source096.plan.table,z.1.Valid 57 3191 := by decide +kernel
private theorem range57From29020To3193 : Segment 57 29020 30493 3191 3193 :=
  paid (pc:=74) (v:=446389754948) (by decide) source096_valid tests57_096_3191 fee57_096_30493 (by decide +kernel)

private theorem range57From29020 : Win 57 29020 30493 :=
  complete (by decide) (by decide) (join_population (join_population range57From29020To2857 range57From29020To2979) (join_population range57From29020To3096 (join_population range57From29020To3191 range57From29020To3193)))

private theorem fee57_093_32291 :
    PopulationFees20258.bill (n:=32291) (PopulationFees20258.tabulate (32291-1) 256) source093.plan.table+
      4*32291*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*341899006064 := by decide +kernel
private theorem range57From30494To2900 : Segment 57 30494 32291 0 2900 :=
  paid (pc:=76) (v:=341899006064) (by decide) source093_valid tests57_093_0 fee57_093_32291 (by decide +kernel)

private theorem tests57_087_2900 : ∀ z∈source087.plan.table,z.1.Valid 57 2900 := by decide +kernel
private theorem fee57_087_32291 :
    PopulationFees20258.bill (n:=32291) (PopulationFees20258.tabulate (32291-1) 256) source087.plan.table+
      4*32291*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*480009249980 := by decide +kernel
private theorem range57From30494To3002 : Segment 57 30494 32291 2900 3002 :=
  paid (pc:=75) (v:=480009249980) (by decide) source087_valid tests57_087_2900 fee57_087_32291 (by decide +kernel)

private theorem tests57_097_3002 : ∀ z∈source097.plan.table,z.1.Valid 57 3002 := by decide +kernel
private theorem fee57_097_32291 :
    PopulationFees20258.bill (n:=32291) (PopulationFees20258.tabulate (32291-1) 256) source097.plan.table+
      4*32291*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*533442500073 := by decide +kernel
private theorem range57From30494To3102 : Segment 57 30494 32291 3002 3102 :=
  paid (pc:=75) (v:=533442500073) (by decide) source097_valid tests57_097_3002 fee57_097_32291 (by decide +kernel)

private theorem tests57_096_3102 : ∀ z∈source096.plan.table,z.1.Valid 57 3102 := by decide +kernel
private theorem fee57_096_32291 :
    PopulationFees20258.bill (n:=32291) (PopulationFees20258.tabulate (32291-1) 256) source096.plan.table+
      4*32291*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*496849802955 := by decide +kernel
private theorem range57From30494To3191 : Segment 57 30494 32291 3102 3191 :=
  paid (pc:=74) (v:=496849802955) (by decide) source096_valid tests57_096_3102 fee57_096_32291 (by decide +kernel)

private theorem range57From30494To3193 : Segment 57 30494 32291 3191 3193 :=
  paid (pc:=74) (v:=496849802955) (by decide) source096_valid tests57_096_3191 fee57_096_32291 (by decide +kernel)

private theorem range57From30494 : Win 57 30494 32291 :=
  complete (by decide) (by decide) (join_population (join_population range57From30494To2900 range57From30494To3002) (join_population range57From30494To3102 (join_population range57From30494To3191 range57From30494To3193)))

private theorem fee57_093_34540 :
    PopulationFees20258.bill (n:=34540) (PopulationFees20258.tabulate (34540-1) 256) source093.plan.table+
      4*34540*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*388043732437 := by decide +kernel
private theorem range57From32292To2944 : Segment 57 32292 34540 0 2944 :=
  paid (pc:=75) (v:=388043732437) (by decide) source093_valid tests57_093_0 fee57_093_34540 (by decide +kernel)

private theorem tests57_097_2944 : ∀ z∈source097.plan.table,z.1.Valid 57 2944 := by decide +kernel
private theorem fee57_097_34540 :
    PopulationFees20258.bill (n:=34540) (PopulationFees20258.tabulate (34540-1) 256) source097.plan.table+
      4*34540*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*604802826471 := by decide +kernel
private theorem range57From32292To3107 : Segment 57 32292 34540 2944 3107 :=
  paid (pc:=75) (v:=604802826471) (by decide) source097_valid tests57_097_2944 fee57_097_34540 (by decide +kernel)

private theorem tests57_096_3107 : ∀ z∈source096.plan.table,z.1.Valid 57 3107 := by decide +kernel
private theorem fee57_096_34540 :
    PopulationFees20258.bill (n:=34540) (PopulationFees20258.tabulate (34540-1) 256) source096.plan.table+
      4*34540*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*563546524679 := by decide +kernel
private theorem range57From32292To3192 : Segment 57 32292 34540 3107 3192 :=
  paid (pc:=74) (v:=563546524679) (by decide) source096_valid tests57_096_3107 fee57_096_34540 (by decide +kernel)

private theorem tests57_096_3192 : ∀ z∈source096.plan.table,z.1.Valid 57 3192 := by decide +kernel
private theorem range57From32292To3193 : Segment 57 32292 34540 3192 3193 :=
  paid (pc:=74) (v:=563546524679) (by decide) source096_valid tests57_096_3192 fee57_096_34540 (by decide +kernel)

private theorem range57From32292 : Win 57 32292 34540 :=
  complete (by decide) (by decide) (join_population (join_population range57From32292To2944 range57From32292To3107) (join_population range57From32292To3192 range57From32292To3193))

private theorem fee57_093_37430 :
    PopulationFees20258.bill (n:=37430) (PopulationFees20258.tabulate (37430-1) 256) source093.plan.table+
      4*37430*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*452014460581 := by decide +kernel
private theorem range57From34541To2991 : Segment 57 34541 37430 0 2991 :=
  paid (pc:=75) (v:=452014460581) (by decide) source093_valid tests57_093_0 fee57_093_37430 (by decide +kernel)

private theorem tests57_090_2991 : ∀ z∈source090.plan.table,z.1.Valid 57 2991 := by decide +kernel
private theorem fee57_090_37430 :
    PopulationFees20258.bill (n:=37430) (PopulationFees20258.tabulate (37430-1) 256) source090.plan.table+
      4*37430*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*585782307358 := by decide +kernel
private theorem range57From34541To3119 : Segment 57 34541 37430 2991 3119 :=
  paid (pc:=74) (v:=585782307358) (by decide) source090_valid tests57_090_2991 fee57_090_37430 (by decide +kernel)

private theorem tests57_096_3119 : ∀ z∈source096.plan.table,z.1.Valid 57 3119 := by decide +kernel
private theorem fee57_096_37430 :
    PopulationFees20258.bill (n:=37430) (PopulationFees20258.tabulate (37430-1) 256) source096.plan.table+
      4*37430*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*655874694209 := by decide +kernel
private theorem range57From34541To3192 : Segment 57 34541 37430 3119 3192 :=
  paid (pc:=74) (v:=655874694209) (by decide) source096_valid tests57_096_3119 fee57_096_37430 (by decide +kernel)

private theorem range57From34541To3193 : Segment 57 34541 37430 3192 3193 :=
  paid (pc:=74) (v:=655874694209) (by decide) source096_valid tests57_096_3192 fee57_096_37430 (by decide +kernel)

private theorem range57From34541 : Win 57 34541 37430 :=
  complete (by decide) (by decide) (join_population (join_population range57From34541To2991 range57From34541To3119) (join_population range57From34541To3192 range57From34541To3193))

private theorem range57From37431 : Win 57 37431 39999 :=
  short (by decide) (by decide)

theorem cut57From29020 : Win 57 29020 39999 :=
  (join_ground (join_ground range57From29020 range57From30494) (join_ground range57From32292 (join_ground range57From34541 range57From37431)))

end JSP233.FiniteCutRanges20258
