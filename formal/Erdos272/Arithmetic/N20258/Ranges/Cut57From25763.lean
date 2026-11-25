module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source092
public import Erdos272.Arithmetic.N20258.Sources.Source093
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests57_093_0 : ∀ z∈source093.plan.table,z.1.Valid 57 0 := by decide +kernel
private theorem fee57_093_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source093.plan.table+
      4*26709*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*239652437830 := by decide +kernel
private theorem range57From25763To2731 : Segment 57 25763 26709 0 2731 :=
  paid (pc:=76) (v:=239652437830) (by decide) source093_valid tests57_093_0 fee57_093_26709 (by decide +kernel)

private theorem tests57_094_2731 : ∀ z∈source094.plan.table,z.1.Valid 57 2731 := by decide +kernel
private theorem fee57_094_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source094.plan.table+
      4*26709*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*357933191508 := by decide +kernel
private theorem range57From25763To2831 : Segment 57 25763 26709 2731 2831 :=
  paid (pc:=76) (v:=357933191508) (by decide) source094_valid tests57_094_2731 fee57_094_26709 (by decide +kernel)

private theorem tests57_092_2831 : ∀ z∈source092.plan.table,z.1.Valid 57 2831 := by decide +kernel
private theorem fee57_092_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source092.plan.table+
      4*26709*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*337579427952 := by decide +kernel
private theorem range57From25763To2909 : Segment 57 25763 26709 2831 2909 :=
  paid (pc:=75) (v:=337579427952) (by decide) source092_valid tests57_092_2831 fee57_092_26709 (by decide +kernel)

private theorem tests57_087_2909 : ∀ z∈source087.plan.table,z.1.Valid 57 2909 := by decide +kernel
private theorem fee57_087_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source087.plan.table+
      4*26709*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*336816085293 := by decide +kernel
private theorem range57From25763To2913 : Segment 57 25763 26709 2909 2913 :=
  paid (pc:=75) (v:=336816085293) (by decide) source087_valid tests57_087_2909 fee57_087_26709 (by decide +kernel)

private theorem tests57_087_2913 : ∀ z∈source087.plan.table,z.1.Valid 57 2913 := by decide +kernel
private theorem range57From25763To2914 : Segment 57 25763 26709 2913 2914 :=
  paid (pc:=75) (v:=336816085293) (by decide) source087_valid tests57_087_2913 fee57_087_26709 (by decide +kernel)

private theorem tests57_097_2914 : ∀ z∈source097.plan.table,z.1.Valid 57 2914 := by decide +kernel
private theorem fee57_097_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source097.plan.table+
      4*26709*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*375224185100 := by decide +kernel
private theorem range57From25763To3073 : Segment 57 25763 26709 2914 3073 :=
  paid (pc:=74) (v:=375224185100) (by decide) source097_valid tests57_097_2914 fee57_097_26709 (by decide +kernel)

private theorem tests57_096_3073 : ∀ z∈source096.plan.table,z.1.Valid 57 3073 := by decide +kernel
private theorem fee57_096_26709 :
    PopulationFees20258.bill (n:=26709) (PopulationFees20258.tabulate (26709-1) 256) source096.plan.table+
      4*26709*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*349066593365 := by decide +kernel
private theorem range57From25763To3190 : Segment 57 25763 26709 3073 3190 :=
  paid (pc:=73) (v:=349066593365) (by decide) source096_valid tests57_096_3073 fee57_096_26709 (by decide +kernel)

private theorem tests57_096_3190 : ∀ z∈source096.plan.table,z.1.Valid 57 3190 := by decide +kernel
private theorem range57From25763To3193 : Segment 57 25763 26709 3190 3193 :=
  paid (pc:=73) (v:=349066593365) (by decide) source096_valid tests57_096_3190 fee57_096_26709 (by decide +kernel)

private theorem range57From25763 : Win 57 25763 26709 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range57From25763To2731 range57From25763To2831) (join_population range57From25763To2909 range57From25763To2913)) (join_population (join_population range57From25763To2914 range57From25763To3073) (join_population range57From25763To3190 range57From25763To3193)))

private theorem fee57_093_27778 :
    PopulationFees20258.bill (n:=27778) (PopulationFees20258.tabulate (27778-1) 256) source093.plan.table+
      4*27778*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*257873122185 := by decide +kernel
private theorem range57From26710To2773 : Segment 57 26710 27778 0 2773 :=
  paid (pc:=76) (v:=257873122185) (by decide) source093_valid tests57_093_0 fee57_093_27778 (by decide +kernel)

private theorem tests57_094_2773 : ∀ z∈source094.plan.table,z.1.Valid 57 2773 := by decide +kernel
private theorem fee57_094_27778 :
    PopulationFees20258.bill (n:=27778) (PopulationFees20258.tabulate (27778-1) 256) source094.plan.table+
      4*27778*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*384811531013 := by decide +kernel
private theorem range57From26710To2861 : Segment 57 26710 27778 2773 2861 :=
  paid (pc:=76) (v:=384811531013) (by decide) source094_valid tests57_094_2773 fee57_094_27778 (by decide +kernel)

private theorem tests57_092_2861 : ∀ z∈source092.plan.table,z.1.Valid 57 2861 := by decide +kernel
private theorem fee57_092_27778 :
    PopulationFees20258.bill (n:=27778) (PopulationFees20258.tabulate (27778-1) 256) source092.plan.table+
      4*27778*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*363178392831 := by decide +kernel
private theorem range57From26710To2934 : Segment 57 26710 27778 2861 2934 :=
  paid (pc:=75) (v:=363178392831) (by decide) source092_valid tests57_092_2861 fee57_092_27778 (by decide +kernel)

private theorem tests57_097_2934 : ∀ z∈source097.plan.table,z.1.Valid 57 2934 := by decide +kernel
private theorem fee57_097_27778 :
    PopulationFees20258.bill (n:=27778) (PopulationFees20258.tabulate (27778-1) 256) source097.plan.table+
      4*27778*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*403427900212 := by decide +kernel
private theorem range57From26710To3081 : Segment 57 26710 27778 2934 3081 :=
  paid (pc:=74) (v:=403427900212) (by decide) source097_valid tests57_097_2934 fee57_097_27778 (by decide +kernel)

private theorem tests57_096_3081 : ∀ z∈source096.plan.table,z.1.Valid 57 3081 := by decide +kernel
private theorem fee57_096_27778 :
    PopulationFees20258.bill (n:=27778) (PopulationFees20258.tabulate (27778-1) 256) source096.plan.table+
      4*27778*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*375401542391 := by decide +kernel
private theorem range57From26710To3191 : Segment 57 26710 27778 3081 3191 :=
  paid (pc:=74) (v:=375401542391) (by decide) source096_valid tests57_096_3081 fee57_096_27778 (by decide +kernel)

private theorem tests57_096_3191 : ∀ z∈source096.plan.table,z.1.Valid 57 3191 := by decide +kernel
private theorem range57From26710To3193 : Segment 57 26710 27778 3191 3193 :=
  paid (pc:=74) (v:=375401542391) (by decide) source096_valid tests57_096_3191 fee57_096_27778 (by decide +kernel)

private theorem range57From26710 : Win 57 26710 27778 :=
  complete (by decide) (by decide) (join_population (join_population range57From26710To2773 (join_population range57From26710To2861 range57From26710To2934)) (join_population range57From26710To3081 (join_population range57From26710To3191 range57From26710To3193)))

private theorem fee57_093_29019 :
    PopulationFees20258.bill (n:=29019) (PopulationFees20258.tabulate (29019-1) 256) source093.plan.table+
      4*29019*NaturalPopulation20258.weights source093.extras≤source093.plan.scale*279790224467 := by decide +kernel
private theorem range57From27779To2815 : Segment 57 27779 29019 0 2815 :=
  paid (pc:=76) (v:=279790224467) (by decide) source093_valid tests57_093_0 fee57_093_29019 (by decide +kernel)

private theorem tests57_094_2815 : ∀ z∈source094.plan.table,z.1.Valid 57 2815 := by decide +kernel
private theorem fee57_094_29019 :
    PopulationFees20258.bill (n:=29019) (PopulationFees20258.tabulate (29019-1) 256) source094.plan.table+
      4*29019*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*417161353032 := by decide +kernel
private theorem range57From27779To2888 : Segment 57 27779 29019 2815 2888 :=
  paid (pc:=76) (v:=417161353032) (by decide) source094_valid tests57_094_2815 fee57_094_29019 (by decide +kernel)

private theorem tests57_087_2888 : ∀ z∈source087.plan.table,z.1.Valid 57 2888 := by decide +kernel
private theorem fee57_087_29019 :
    PopulationFees20258.bill (n:=29019) (PopulationFees20258.tabulate (29019-1) 256) source087.plan.table+
      4*29019*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*393151760865 := by decide +kernel
private theorem range57From27779To2958 : Segment 57 27779 29019 2888 2958 :=
  paid (pc:=75) (v:=393151760865) (by decide) source087_valid tests57_087_2888 fee57_087_29019 (by decide +kernel)

private theorem tests57_097_2958 : ∀ z∈source097.plan.table,z.1.Valid 57 2958 := by decide +kernel
private theorem fee57_097_29019 :
    PopulationFees20258.bill (n:=29019) (PopulationFees20258.tabulate (29019-1) 256) source097.plan.table+
      4*29019*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*437363483062 := by decide +kernel
private theorem range57From27779To3088 : Segment 57 27779 29019 2958 3088 :=
  paid (pc:=75) (v:=437363483062) (by decide) source097_valid tests57_097_2958 fee57_097_29019 (by decide +kernel)

private theorem tests57_096_3088 : ∀ z∈source096.plan.table,z.1.Valid 57 3088 := by decide +kernel
private theorem fee57_096_29019 :
    PopulationFees20258.bill (n:=29019) (PopulationFees20258.tabulate (29019-1) 256) source096.plan.table+
      4*29019*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*407075147262 := by decide +kernel
private theorem range57From27779To3191 : Segment 57 27779 29019 3088 3191 :=
  paid (pc:=74) (v:=407075147262) (by decide) source096_valid tests57_096_3088 fee57_096_29019 (by decide +kernel)

private theorem range57From27779To3193 : Segment 57 27779 29019 3191 3193 :=
  paid (pc:=74) (v:=407075147262) (by decide) source096_valid tests57_096_3191 fee57_096_29019 (by decide +kernel)

private theorem range57From27779 : Win 57 27779 29019 :=
  complete (by decide) (by decide) (join_population (join_population range57From27779To2815 (join_population range57From27779To2888 range57From27779To2958)) (join_population range57From27779To3088 (join_population range57From27779To3191 range57From27779To3193)))

theorem cut57From25763 : Win 57 25763 29019 :=
  (join_ground range57From25763 (join_ground range57From26710 range57From27779))

end JSP233.FiniteCutRanges20258
