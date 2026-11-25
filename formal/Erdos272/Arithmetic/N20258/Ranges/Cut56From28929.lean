module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source088
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source092

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests56_088_0 : ∀ z∈source088.plan.table,z.1.Valid 56 0 := by decide +kernel
private theorem fee56_088_30349 :
    PopulationFees20258.bill (n:=30349) (PopulationFees20258.tabulate (30349-1) 256) source088.plan.table+
      4*30349*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*324789692435 := by decide +kernel
private theorem range56From28929To2821 : Segment 56 28929 30349 0 2821 :=
  paid (pc:=76) (v:=324789692435) (by decide) source088_valid tests56_088_0 fee56_088_30349 (by decide +kernel)

private theorem tests56_092_2821 : ∀ z∈source092.plan.table,z.1.Valid 56 2821 := by decide +kernel
private theorem fee56_092_30349 :
    PopulationFees20258.bill (n:=30349) (PopulationFees20258.tabulate (30349-1) 256) source092.plan.table+
      4*30349*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*428117557316 := by decide +kernel
private theorem range56From28929To2990 : Segment 56 28929 30349 2821 2990 :=
  paid (pc:=75) (v:=428117557316) (by decide) source092_valid tests56_092_2821 fee56_092_30349 (by decide +kernel)

private theorem tests56_090_2990 : ∀ z∈source090.plan.table,z.1.Valid 56 2990 := by decide +kernel
private theorem fee56_090_30349 :
    PopulationFees20258.bill (n:=30349) (PopulationFees20258.tabulate (30349-1) 256) source090.plan.table+
      4*30349*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*394679572614 := by decide +kernel
private theorem range56From28929To3079 : Segment 56 28929 30349 2990 3079 :=
  paid (pc:=75) (v:=394679572614) (by decide) source090_valid tests56_090_2990 fee56_090_30349 (by decide +kernel)

private theorem tests56_090_3079 : ∀ z∈source090.plan.table,z.1.Valid 56 3079 := by decide +kernel
private theorem range56From28929To3081 : Segment 56 28929 30349 3079 3081 :=
  paid (pc:=75) (v:=394679572614) (by decide) source090_valid tests56_090_3079 fee56_090_30349 (by decide +kernel)

private theorem range56From28929 : Win 56 28929 30349 :=
  complete (by decide) (by decide) (join_population (join_population range56From28929To2821 range56From28929To2990) (join_population range56From28929To3079 range56From28929To3081))

private theorem fee56_088_32128 :
    PopulationFees20258.bill (n:=32128) (PopulationFees20258.tabulate (32128-1) 256) source088.plan.table+
      4*32128*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*361363142445 := by decide +kernel
private theorem range56From30350To2850 : Segment 56 30350 32128 0 2850 :=
  paid (pc:=76) (v:=361363142445) (by decide) source088_valid tests56_088_0 fee56_088_32128 (by decide +kernel)

private theorem tests56_087_2850 : ∀ z∈source087.plan.table,z.1.Valid 56 2850 := by decide +kernel
private theorem fee56_087_32128 :
    PopulationFees20258.bill (n:=32128) (PopulationFees20258.tabulate (32128-1) 256) source087.plan.table+
      4*32128*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*475385435567 := by decide +kernel
private theorem range56From30350To2996 : Segment 56 30350 32128 2850 2996 :=
  paid (pc:=75) (v:=475385435567) (by decide) source087_valid tests56_087_2850 fee56_087_32128 (by decide +kernel)

private theorem tests56_090_2996 : ∀ z∈source090.plan.table,z.1.Valid 56 2996 := by decide +kernel
private theorem fee56_090_32128 :
    PopulationFees20258.bill (n:=32128) (PopulationFees20258.tabulate (32128-1) 256) source090.plan.table+
      4*32128*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*439121301168 := by decide +kernel
private theorem range56From30350To3080 : Segment 56 30350 32128 2996 3080 :=
  paid (pc:=75) (v:=439121301168) (by decide) source090_valid tests56_090_2996 fee56_090_32128 (by decide +kernel)

private theorem tests56_090_3080 : ∀ z∈source090.plan.table,z.1.Valid 56 3080 := by decide +kernel
private theorem range56From30350To3081 : Segment 56 30350 32128 3080 3081 :=
  paid (pc:=75) (v:=439121301168) (by decide) source090_valid tests56_090_3080 fee56_090_32128 (by decide +kernel)

private theorem range56From30350 : Win 56 30350 32128 :=
  complete (by decide) (by decide) (join_population (join_population range56From30350To2850 range56From30350To2996) (join_population range56From30350To3080 range56From30350To3081))

private theorem fee56_088_34404 :
    PopulationFees20258.bill (n:=34404) (PopulationFees20258.tabulate (34404-1) 256) source088.plan.table+
      4*34404*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*411227331536 := by decide +kernel
private theorem range56From32129To2881 : Segment 56 32129 34404 0 2881 :=
  paid (pc:=76) (v:=411227331536) (by decide) source088_valid tests56_088_0 fee56_088_34404 (by decide +kernel)

private theorem tests56_087_2881 : ∀ z∈source087.plan.table,z.1.Valid 56 2881 := by decide +kernel
private theorem fee56_087_34404 :
    PopulationFees20258.bill (n:=34404) (PopulationFees20258.tabulate (34404-1) 256) source087.plan.table+
      4*34404*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*540868342463 := by decide +kernel
private theorem range56From32129To3001 : Segment 56 32129 34404 2881 3001 :=
  paid (pc:=75) (v:=540868342463) (by decide) source087_valid tests56_087_2881 fee56_087_34404 (by decide +kernel)

private theorem tests56_090_3001 : ∀ z∈source090.plan.table,z.1.Valid 56 3001 := by decide +kernel
private theorem fee56_090_34404 :
    PopulationFees20258.bill (n:=34404) (PopulationFees20258.tabulate (34404-1) 256) source090.plan.table+
      4*34404*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*499663632027 := by decide +kernel
private theorem range56From32129To3079 : Segment 56 32129 34404 3001 3079 :=
  paid (pc:=75) (v:=499663632027) (by decide) source090_valid tests56_090_3001 fee56_090_34404 (by decide +kernel)

private theorem range56From32129To3081 : Segment 56 32129 34404 3079 3081 :=
  paid (pc:=75) (v:=499663632027) (by decide) source090_valid tests56_090_3079 fee56_090_34404 (by decide +kernel)

private theorem range56From32129 : Win 56 32129 34404 :=
  complete (by decide) (by decide) (join_population (join_population range56From32129To2881 range56From32129To3001) (join_population range56From32129To3079 range56From32129To3081))

private theorem fee56_088_37392 :
    PopulationFees20258.bill (n:=37392) (PopulationFees20258.tabulate (37392-1) 256) source088.plan.table+
      4*37392*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*481322890110 := by decide +kernel
private theorem range56From34405To2915 : Segment 56 34405 37392 0 2915 :=
  paid (pc:=75) (v:=481322890110) (by decide) source088_valid tests56_088_0 fee56_088_37392 (by decide +kernel)

private theorem tests56_090_2915 : ∀ z∈source090.plan.table,z.1.Valid 56 2915 := by decide +kernel
private theorem fee56_090_37392 :
    PopulationFees20258.bill (n:=37392) (PopulationFees20258.tabulate (37392-1) 256) source090.plan.table+
      4*37392*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*584761722866 := by decide +kernel
private theorem range56From34405To3081 : Segment 56 34405 37392 2915 3081 :=
  paid (pc:=74) (v:=584761722866) (by decide) source090_valid tests56_090_2915 fee56_090_37392 (by decide +kernel)

private theorem range56From34405 : Win 56 34405 37392 :=
  complete (by decide) (by decide) (join_population range56From34405To2915 range56From34405To3081)

private theorem range56From37393 : Win 56 37393 39999 :=
  short (by decide) (by decide)

theorem cut56From28929 : Win 56 28929 39999 :=
  (join_ground (join_ground range56From28929 range56From30350) (join_ground range56From32129 (join_ground range56From34405 range56From37393)))

end JSP233.FiniteCutRanges20258
