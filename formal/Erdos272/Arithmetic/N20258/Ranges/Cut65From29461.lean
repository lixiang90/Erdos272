module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source109
public import Erdos272.Arithmetic.N20258.Sources.Source111
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source115
public import Erdos272.Arithmetic.N20258.Sources.Source116

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests65_116_0 : ∀ z∈source116.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_116_30407 :
    PopulationFees20258.bill (n:=30407) (PopulationFees20258.tabulate (30407-1) 256) source116.plan.table+
      4*30407*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*349768232400 := by decide +kernel
private theorem range65From29461To3661 : Segment 65 29461 30407 0 3661 :=
  paid (pc:=74) (v:=349768232400) (by decide) source116_valid tests65_116_0 fee65_116_30407 (by decide +kernel)

private theorem tests65_109_3661 : ∀ z∈source109.plan.table,z.1.Valid 65 3661 := by decide +kernel
private theorem fee65_109_30407 :
    PopulationFees20258.bill (n:=30407) (PopulationFees20258.tabulate (30407-1) 256) source109.plan.table+
      4*30407*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*420356817433 := by decide +kernel
private theorem range65From29461To3810 : Segment 65 29461 30407 3661 3810 :=
  paid (pc:=73) (v:=420356817433) (by decide) source109_valid tests65_109_3661 fee65_109_30407 (by decide +kernel)

private theorem tests65_111_3810 : ∀ z∈source111.plan.table,z.1.Valid 65 3810 := by decide +kernel
private theorem fee65_111_30407 :
    PopulationFees20258.bill (n:=30407) (PopulationFees20258.tabulate (30407-1) 256) source111.plan.table+
      4*30407*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*451930221364 := by decide +kernel
private theorem range65From29461To4121 : Segment 65 29461 30407 3810 4121 :=
  paid (pc:=71) (v:=451930221364) (by decide) source111_valid tests65_111_3810 fee65_111_30407 (by decide +kernel)

private theorem tests65_112_4121 : ∀ z∈source112.plan.table,z.1.Valid 65 4121 := by decide +kernel
private theorem fee65_112_30407 :
    PopulationFees20258.bill (n:=30407) (PopulationFees20258.tabulate (30407-1) 256) source112.plan.table+
      4*30407*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*443916628797 := by decide +kernel
private theorem range65From29461To4161 : Segment 65 29461 30407 4121 4161 :=
  paid (pc:=70) (v:=443916628797) (by decide) source112_valid tests65_112_4121 fee65_112_30407 (by decide +kernel)

private theorem range65From29461 : Win 65 29461 30407 :=
  complete (by decide) (by decide) (join_population (join_population range65From29461To3661 range65From29461To3810) (join_population range65From29461To4121 range65From29461To4161))

private theorem fee65_116_31390 :
    PopulationFees20258.bill (n:=31390) (PopulationFees20258.tabulate (31390-1) 256) source116.plan.table+
      4*31390*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*371162362247 := by decide +kernel
private theorem range65From30408To3706 : Segment 65 30408 31390 0 3706 :=
  paid (pc:=74) (v:=371162362247) (by decide) source116_valid tests65_116_0 fee65_116_31390 (by decide +kernel)

private theorem tests65_109_3706 : ∀ z∈source109.plan.table,z.1.Valid 65 3706 := by decide +kernel
private theorem fee65_109_31390 :
    PopulationFees20258.bill (n:=31390) (PopulationFees20258.tabulate (31390-1) 256) source109.plan.table+
      4*31390*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*446205137878 := by decide +kernel
private theorem range65From30408To3841 : Segment 65 30408 31390 3706 3841 :=
  paid (pc:=73) (v:=446205137878) (by decide) source109_valid tests65_109_3706 fee65_109_31390 (by decide +kernel)

private theorem tests65_112_3841 : ∀ z∈source112.plan.table,z.1.Valid 65 3841 := by decide +kernel
private theorem fee65_112_31390 :
    PopulationFees20258.bill (n:=31390) (PopulationFees20258.tabulate (31390-1) 256) source112.plan.table+
      4*31390*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*470993963450 := by decide +kernel
private theorem range65From30408To4154 : Segment 65 30408 31390 3841 4154 :=
  paid (pc:=71) (v:=470993963450) (by decide) source112_valid tests65_112_3841 fee65_112_31390 (by decide +kernel)

private theorem tests65_112_4154 : ∀ z∈source112.plan.table,z.1.Valid 65 4154 := by decide +kernel
private theorem range65From30408To4161 : Segment 65 30408 31390 4154 4161 :=
  paid (pc:=71) (v:=470993963450) (by decide) source112_valid tests65_112_4154 fee65_112_31390 (by decide +kernel)

private theorem range65From30408 : Win 65 30408 31390 :=
  complete (by decide) (by decide) (join_population (join_population range65From30408To3706 range65From30408To3841) (join_population range65From30408To4154 range65From30408To4161))

private theorem fee65_116_32442 :
    PopulationFees20258.bill (n:=32442) (PopulationFees20258.tabulate (32442-1) 256) source116.plan.table+
      4*32442*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*394417001516 := by decide +kernel
private theorem range65From31391To3748 : Segment 65 31391 32442 0 3748 :=
  paid (pc:=74) (v:=394417001516) (by decide) source116_valid tests65_116_0 fee65_116_32442 (by decide +kernel)

private theorem tests65_109_3748 : ∀ z∈source109.plan.table,z.1.Valid 65 3748 := by decide +kernel
private theorem fee65_109_32442 :
    PopulationFees20258.bill (n:=32442) (PopulationFees20258.tabulate (32442-1) 256) source109.plan.table+
      4*32442*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*474427170195 := by decide +kernel
private theorem range65From31391To3869 : Segment 65 31391 32442 3748 3869 :=
  paid (pc:=74) (v:=474427170195) (by decide) source109_valid tests65_109_3748 fee65_109_32442 (by decide +kernel)

private theorem tests65_112_3869 : ∀ z∈source112.plan.table,z.1.Valid 65 3869 := by decide +kernel
private theorem fee65_112_32442 :
    PopulationFees20258.bill (n:=32442) (PopulationFees20258.tabulate (32442-1) 256) source112.plan.table+
      4*32442*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*500765978153 := by decide +kernel
private theorem range65From31391To4155 : Segment 65 31391 32442 3869 4155 :=
  paid (pc:=72) (v:=500765978153) (by decide) source112_valid tests65_112_3869 fee65_112_32442 (by decide +kernel)

private theorem tests65_112_4155 : ∀ z∈source112.plan.table,z.1.Valid 65 4155 := by decide +kernel
private theorem range65From31391To4161 : Segment 65 31391 32442 4155 4161 :=
  paid (pc:=72) (v:=500765978153) (by decide) source112_valid tests65_112_4155 fee65_112_32442 (by decide +kernel)

private theorem range65From31391 : Win 65 31391 32442 :=
  complete (by decide) (by decide) (join_population (join_population range65From31391To3748 range65From31391To3869) (join_population range65From31391To4155 range65From31391To4161))

private theorem tests65_115_0 : ∀ z∈source115.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_115_33598 :
    PopulationFees20258.bill (n:=33598) (PopulationFees20258.tabulate (33598-1) 256) source115.plan.table+
      4*33598*NaturalPopulation20258.weights source115.extras≤source115.plan.scale*421133064505 := by decide +kernel
private theorem range65From32443To3785 : Segment 65 32443 33598 0 3785 :=
  paid (pc:=75) (v:=421133064505) (by decide) source115_valid tests65_115_0 fee65_115_33598 (by decide +kernel)

private theorem tests65_111_3785 : ∀ z∈source111.plan.table,z.1.Valid 65 3785 := by decide +kernel
private theorem fee65_111_33598 :
    PopulationFees20258.bill (n:=33598) (PopulationFees20258.tabulate (33598-1) 256) source111.plan.table+
      4*33598*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*544125546450 := by decide +kernel
private theorem range65From32443To4129 : Segment 65 32443 33598 3785 4129 :=
  paid (pc:=73) (v:=544125546450) (by decide) source111_valid tests65_111_3785 fee65_111_33598 (by decide +kernel)

private theorem tests65_112_4129 : ∀ z∈source112.plan.table,z.1.Valid 65 4129 := by decide +kernel
private theorem fee65_112_33598 :
    PopulationFees20258.bill (n:=33598) (PopulationFees20258.tabulate (33598-1) 256) source112.plan.table+
      4*33598*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*534607709110 := by decide +kernel
private theorem range65From32443To4161 : Segment 65 32443 33598 4129 4161 :=
  paid (pc:=72) (v:=534607709110) (by decide) source112_valid tests65_112_4129 fee65_112_33598 (by decide +kernel)

private theorem range65From32443 : Win 65 32443 33598 :=
  complete (by decide) (by decide) (join_population range65From32443To3785 (join_population range65From32443To4129 range65From32443To4161))

private theorem fee65_115_34903 :
    PopulationFees20258.bill (n:=34903) (PopulationFees20258.tabulate (34903-1) 256) source115.plan.table+
      4*34903*NaturalPopulation20258.weights source115.extras≤source115.plan.scale*452529311939 := by decide +kernel
private theorem range65From33599To3821 : Segment 65 33599 34903 0 3821 :=
  paid (pc:=75) (v:=452529311939) (by decide) source115_valid tests65_115_0 fee65_115_34903 (by decide +kernel)

private theorem tests65_112_3821 : ∀ z∈source112.plan.table,z.1.Valid 65 3821 := by decide +kernel
private theorem fee65_112_34903 :
    PopulationFees20258.bill (n:=34903) (PopulationFees20258.tabulate (34903-1) 256) source112.plan.table+
      4*34903*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*574278430719 := by decide +kernel
private theorem range65From33599To4154 : Segment 65 33599 34903 3821 4154 :=
  paid (pc:=73) (v:=574278430719) (by decide) source112_valid tests65_112_3821 fee65_112_34903 (by decide +kernel)

private theorem range65From33599To4161 : Segment 65 33599 34903 4154 4161 :=
  paid (pc:=73) (v:=574278430719) (by decide) source112_valid tests65_112_4154 fee65_112_34903 (by decide +kernel)

private theorem range65From33599 : Win 65 33599 34903 :=
  complete (by decide) (by decide) (join_population range65From33599To3821 (join_population range65From33599To4154 range65From33599To4161))

private theorem fee65_116_36414 :
    PopulationFees20258.bill (n:=36414) (PopulationFees20258.tabulate (36414-1) 256) source116.plan.table+
      4*36414*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*489725778074 := by decide +kernel
private theorem range65From34904To3857 : Segment 65 34904 36414 0 3857 :=
  paid (pc:=75) (v:=489725778074) (by decide) source116_valid tests65_116_0 fee65_116_36414 (by decide +kernel)

private theorem tests65_112_3857 : ∀ z∈source112.plan.table,z.1.Valid 65 3857 := by decide +kernel
private theorem fee65_112_36414 :
    PopulationFees20258.bill (n:=36414) (PopulationFees20258.tabulate (36414-1) 256) source112.plan.table+
      4*36414*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*621702633983 := by decide +kernel
private theorem range65From34904To4156 : Segment 65 34904 36414 3857 4156 :=
  paid (pc:=73) (v:=621702633983) (by decide) source112_valid tests65_112_3857 fee65_112_36414 (by decide +kernel)

private theorem tests65_112_4156 : ∀ z∈source112.plan.table,z.1.Valid 65 4156 := by decide +kernel
private theorem range65From34904To4161 : Segment 65 34904 36414 4156 4161 :=
  paid (pc:=73) (v:=621702633983) (by decide) source112_valid tests65_112_4156 fee65_112_36414 (by decide +kernel)

private theorem range65From34904 : Win 65 34904 36414 :=
  complete (by decide) (by decide) (join_population range65From34904To3857 (join_population range65From34904To4156 range65From34904To4161))

private theorem fee65_116_38205 :
    PopulationFees20258.bill (n:=38205) (PopulationFees20258.tabulate (38205-1) 256) source116.plan.table+
      4*38205*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*536196349758 := by decide +kernel
private theorem range65From36415To3892 : Segment 65 36415 38205 0 3892 :=
  paid (pc:=75) (v:=536196349758) (by decide) source116_valid tests65_116_0 fee65_116_38205 (by decide +kernel)

private theorem tests65_112_3892 : ∀ z∈source112.plan.table,z.1.Valid 65 3892 := by decide +kernel
private theorem fee65_112_38205 :
    PopulationFees20258.bill (n:=38205) (PopulationFees20258.tabulate (38205-1) 256) source112.plan.table+
      4*38205*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*680805237923 := by decide +kernel
private theorem range65From36415To4156 : Segment 65 36415 38205 3892 4156 :=
  paid (pc:=74) (v:=680805237923) (by decide) source112_valid tests65_112_3892 fee65_112_38205 (by decide +kernel)

private theorem range65From36415To4161 : Segment 65 36415 38205 4156 4161 :=
  paid (pc:=74) (v:=680805237923) (by decide) source112_valid tests65_112_4156 fee65_112_38205 (by decide +kernel)

private theorem range65From36415 : Win 65 36415 38205 :=
  complete (by decide) (by decide) (join_population range65From36415To3892 (join_population range65From36415To4156 range65From36415To4161))

theorem cut65From29461 : Win 65 29461 38205 :=
  (join_ground (join_ground range65From29461 (join_ground range65From30408 range65From31391)) (join_ground (join_ground range65From32443 range65From33599) (join_ground range65From34904 range65From36415)))

end JSP233.FiniteCutRanges20258
