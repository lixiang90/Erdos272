module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source088
public import Erdos272.Arithmetic.N20258.Sources.Source089
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source092

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests56_088_0 : ∀ z∈source088.plan.table,z.1.Valid 56 0 := by decide +kernel
private theorem fee56_088_25276 :
    PopulationFees20258.bill (n:=25276) (PopulationFees20258.tabulate (25276-1) 256) source088.plan.table+
      4*25276*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*231029866834 := by decide +kernel
private theorem range56From24657To2696 : Segment 56 24657 25276 0 2696 :=
  paid (pc:=77) (v:=231029866834) (by decide) source088_valid tests56_088_0 fee56_088_25276 (by decide +kernel)

private theorem tests56_089_2696 : ∀ z∈source089.plan.table,z.1.Valid 56 2696 := by decide +kernel
private theorem fee56_089_25276 :
    PopulationFees20258.bill (n:=25276) (PopulationFees20258.tabulate (25276-1) 256) source089.plan.table+
      4*25276*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*340537956890 := by decide +kernel
private theorem range56From24657To2811 : Segment 56 24657 25276 2696 2811 :=
  paid (pc:=76) (v:=340537956890) (by decide) source089_valid tests56_089_2696 fee56_089_25276 (by decide +kernel)

private theorem tests56_092_2811 : ∀ z∈source092.plan.table,z.1.Valid 56 2811 := by decide +kernel
private theorem fee56_092_25276 :
    PopulationFees20258.bill (n:=25276) (PopulationFees20258.tabulate (25276-1) 256) source092.plan.table+
      4*25276*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*305072801576 := by decide +kernel
private theorem range56From24657To2967 : Segment 56 24657 25276 2811 2967 :=
  paid (pc:=75) (v:=305072801576) (by decide) source092_valid tests56_092_2811 fee56_092_25276 (by decide +kernel)

private theorem tests56_090_2967 : ∀ z∈source090.plan.table,z.1.Valid 56 2967 := by decide +kernel
private theorem fee56_090_25276 :
    PopulationFees20258.bill (n:=25276) (PopulationFees20258.tabulate (25276-1) 256) source090.plan.table+
      4*25276*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*280820720115 := by decide +kernel
private theorem range56From24657To3078 : Segment 56 24657 25276 2967 3078 :=
  paid (pc:=74) (v:=280820720115) (by decide) source090_valid tests56_090_2967 fee56_090_25276 (by decide +kernel)

private theorem tests56_090_3078 : ∀ z∈source090.plan.table,z.1.Valid 56 3078 := by decide +kernel
private theorem range56From24657To3081 : Segment 56 24657 25276 3078 3081 :=
  paid (pc:=74) (v:=280820720115) (by decide) source090_valid tests56_090_3078 fee56_090_25276 (by decide +kernel)

private theorem range56From24657 : Win 56 24657 25276 :=
  complete (by decide) (by decide) (join_population (join_population range56From24657To2696 range56From24657To2811) (join_population range56From24657To2967 (join_population range56From24657To3078 range56From24657To3081)))

private theorem fee56_088_25983 :
    PopulationFees20258.bill (n:=25983) (PopulationFees20258.tabulate (25983-1) 256) source088.plan.table+
      4*25983*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*243094000841 := by decide +kernel
private theorem range56From25277To2719 : Segment 56 25277 25983 0 2719 :=
  paid (pc:=77) (v:=243094000841) (by decide) source088_valid tests56_088_0 fee56_088_25983 (by decide +kernel)

private theorem tests56_089_2719 : ∀ z∈source089.plan.table,z.1.Valid 56 2719 := by decide +kernel
private theorem fee56_089_25983 :
    PopulationFees20258.bill (n:=25983) (PopulationFees20258.tabulate (25983-1) 256) source089.plan.table+
      4*25983*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*358156862138 := by decide +kernel
private theorem range56From25277To2821 : Segment 56 25277 25983 2719 2821 :=
  paid (pc:=76) (v:=358156862138) (by decide) source089_valid tests56_089_2719 fee56_089_25983 (by decide +kernel)

private theorem tests56_092_2821 : ∀ z∈source092.plan.table,z.1.Valid 56 2821 := by decide +kernel
private theorem fee56_092_25983 :
    PopulationFees20258.bill (n:=25983) (PopulationFees20258.tabulate (25983-1) 256) source092.plan.table+
      4*25983*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*320906961130 := by decide +kernel
private theorem range56From25277To2972 : Segment 56 25277 25983 2821 2972 :=
  paid (pc:=75) (v:=320906961130) (by decide) source092_valid tests56_092_2821 fee56_092_25983 (by decide +kernel)

private theorem tests56_090_2972 : ∀ z∈source090.plan.table,z.1.Valid 56 2972 := by decide +kernel
private theorem fee56_090_25983 :
    PopulationFees20258.bill (n:=25983) (PopulationFees20258.tabulate (25983-1) 256) source090.plan.table+
      4*25983*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*295467647286 := by decide +kernel
private theorem range56From25277To3079 : Segment 56 25277 25983 2972 3079 :=
  paid (pc:=75) (v:=295467647286) (by decide) source090_valid tests56_090_2972 fee56_090_25983 (by decide +kernel)

private theorem tests56_090_3079 : ∀ z∈source090.plan.table,z.1.Valid 56 3079 := by decide +kernel
private theorem range56From25277To3081 : Segment 56 25277 25983 3079 3081 :=
  paid (pc:=75) (v:=295467647286) (by decide) source090_valid tests56_090_3079 fee56_090_25983 (by decide +kernel)

private theorem range56From25277 : Win 56 25277 25983 :=
  complete (by decide) (by decide) (join_population (join_population range56From25277To2719 range56From25277To2821) (join_population range56From25277To2972 (join_population range56From25277To3079 range56From25277To3081)))

private theorem fee56_088_26801 :
    PopulationFees20258.bill (n:=26801) (PopulationFees20258.tabulate (26801-1) 256) source088.plan.table+
      4*26801*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*257550968289 := by decide +kernel
private theorem range56From25984To2742 : Segment 56 25984 26801 0 2742 :=
  paid (pc:=77) (v:=257550968289) (by decide) source088_valid tests56_088_0 fee56_088_26801 (by decide +kernel)

private theorem tests56_085_2742 : ∀ z∈source085.plan.table,z.1.Valid 56 2742 := by decide +kernel
private theorem fee56_085_26801 :
    PopulationFees20258.bill (n:=26801) (PopulationFees20258.tabulate (26801-1) 256) source085.plan.table+
      4*26801*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*364838157684 := by decide +kernel
private theorem range56From25984To2883 : Segment 56 25984 26801 2742 2883 :=
  paid (pc:=76) (v:=364838157684) (by decide) source085_valid tests56_085_2742 fee56_085_26801 (by decide +kernel)

private theorem tests56_087_2883 : ∀ z∈source087.plan.table,z.1.Valid 56 2883 := by decide +kernel
private theorem fee56_087_26801 :
    PopulationFees20258.bill (n:=26801) (PopulationFees20258.tabulate (26801-1) 256) source087.plan.table+
      4*26801*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*339101529880 := by decide +kernel
private theorem range56From25984To2980 : Segment 56 25984 26801 2883 2980 :=
  paid (pc:=75) (v:=339101529880) (by decide) source087_valid tests56_087_2883 fee56_087_26801 (by decide +kernel)

private theorem tests56_090_2980 : ∀ z∈source090.plan.table,z.1.Valid 56 2980 := by decide +kernel
private theorem fee56_090_26801 :
    PopulationFees20258.bill (n:=26801) (PopulationFees20258.tabulate (26801-1) 256) source090.plan.table+
      4*26801*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*313032421164 := by decide +kernel
private theorem range56From25984To3079 : Segment 56 25984 26801 2980 3079 :=
  paid (pc:=75) (v:=313032421164) (by decide) source090_valid tests56_090_2980 fee56_090_26801 (by decide +kernel)

private theorem range56From25984To3081 : Segment 56 25984 26801 3079 3081 :=
  paid (pc:=75) (v:=313032421164) (by decide) source090_valid tests56_090_3079 fee56_090_26801 (by decide +kernel)

private theorem range56From25984 : Win 56 25984 26801 :=
  complete (by decide) (by decide) (join_population (join_population range56From25984To2742 range56From25984To2883) (join_population range56From25984To2980 (join_population range56From25984To3079 range56From25984To3081)))

private theorem fee56_088_27768 :
    PopulationFees20258.bill (n:=27768) (PopulationFees20258.tabulate (27768-1) 256) source088.plan.table+
      4*27768*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*275034423875 := by decide +kernel
private theorem range56From26802To2767 : Segment 56 26802 27768 0 2767 :=
  paid (pc:=77) (v:=275034423875) (by decide) source088_valid tests56_088_0 fee56_088_27768 (by decide +kernel)

private theorem tests56_085_2767 : ∀ z∈source085.plan.table,z.1.Valid 56 2767 := by decide +kernel
private theorem fee56_085_27768 :
    PopulationFees20258.bill (n:=27768) (PopulationFees20258.tabulate (27768-1) 256) source085.plan.table+
      4*27768*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*389447685906 := by decide +kernel
private theorem range56From26802To2893 : Segment 56 26802 27768 2767 2893 :=
  paid (pc:=76) (v:=389447685906) (by decide) source085_valid tests56_085_2767 fee56_085_27768 (by decide +kernel)

private theorem tests56_080_2893 : ∀ z∈source080.plan.table,z.1.Valid 56 2893 := by decide +kernel
private theorem fee56_080_27768 :
    PopulationFees20258.bill (n:=27768) (PopulationFees20258.tabulate (27768-1) 256) source080.plan.table+
      4*27768*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*358682126214 := by decide +kernel
private theorem range56From26802To2996 : Segment 56 26802 27768 2893 2996 :=
  paid (pc:=75) (v:=358682126214) (by decide) source080_valid tests56_080_2893 fee56_080_27768 (by decide +kernel)

private theorem tests56_090_2996 : ∀ z∈source090.plan.table,z.1.Valid 56 2996 := by decide +kernel
private theorem fee56_090_27768 :
    PopulationFees20258.bill (n:=27768) (PopulationFees20258.tabulate (27768-1) 256) source090.plan.table+
      4*27768*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*334266582352 := by decide +kernel
private theorem range56From26802To3079 : Segment 56 26802 27768 2996 3079 :=
  paid (pc:=75) (v:=334266582352) (by decide) source090_valid tests56_090_2996 fee56_090_27768 (by decide +kernel)

private theorem range56From26802To3081 : Segment 56 26802 27768 3079 3081 :=
  paid (pc:=75) (v:=334266582352) (by decide) source090_valid tests56_090_3079 fee56_090_27768 (by decide +kernel)

private theorem range56From26802 : Win 56 26802 27768 :=
  complete (by decide) (by decide) (join_population (join_population range56From26802To2767 range56From26802To2893) (join_population range56From26802To2996 (join_population range56From26802To3079 range56From26802To3081)))

private theorem fee56_088_28928 :
    PopulationFees20258.bill (n:=28928) (PopulationFees20258.tabulate (28928-1) 256) source088.plan.table+
      4*28928*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*296897356861 := by decide +kernel
private theorem range56From27769To2793 : Segment 56 27769 28928 0 2793 :=
  paid (pc:=77) (v:=296897356861) (by decide) source088_valid tests56_088_0 fee56_088_28928 (by decide +kernel)

private theorem tests56_092_2793 : ∀ z∈source092.plan.table,z.1.Valid 56 2793 := by decide +kernel
private theorem fee56_092_28928 :
    PopulationFees20258.bill (n:=28928) (PopulationFees20258.tabulate (28928-1) 256) source092.plan.table+
      4*28928*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*391536497827 := by decide +kernel
private theorem range56From27769To2984 : Segment 56 27769 28928 2793 2984 :=
  paid (pc:=76) (v:=391536497827) (by decide) source092_valid tests56_092_2793 fee56_092_28928 (by decide +kernel)

private theorem tests56_090_2984 : ∀ z∈source090.plan.table,z.1.Valid 56 2984 := by decide +kernel
private theorem fee56_090_28928 :
    PopulationFees20258.bill (n:=28928) (PopulationFees20258.tabulate (28928-1) 256) source090.plan.table+
      4*28928*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*360813114745 := by decide +kernel
private theorem range56From27769To3080 : Segment 56 27769 28928 2984 3080 :=
  paid (pc:=75) (v:=360813114745) (by decide) source090_valid tests56_090_2984 fee56_090_28928 (by decide +kernel)

private theorem tests56_090_3080 : ∀ z∈source090.plan.table,z.1.Valid 56 3080 := by decide +kernel
private theorem range56From27769To3081 : Segment 56 27769 28928 3080 3081 :=
  paid (pc:=75) (v:=360813114745) (by decide) source090_valid tests56_090_3080 fee56_090_28928 (by decide +kernel)

private theorem range56From27769 : Win 56 27769 28928 :=
  complete (by decide) (by decide) (join_population (join_population range56From27769To2793 range56From27769To2984) (join_population range56From27769To3080 range56From27769To3081))

theorem cut56From24657 : Win 56 24657 28928 :=
  (join_ground (join_ground range56From24657 range56From25277) (join_ground range56From25984 (join_ground range56From26802 range56From27769)))

end JSP233.FiniteCutRanges20258
