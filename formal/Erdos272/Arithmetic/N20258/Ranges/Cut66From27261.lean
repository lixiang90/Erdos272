module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source111
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source117

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests66_117_0 : ∀ z∈source117.plan.table,z.1.Valid 66 0 := by decide +kernel
private theorem fee66_117_28052 :
    PopulationFees20258.bill (n:=28052) (PopulationFees20258.tabulate (28052-1) 256) source117.plan.table+
      4*28052*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*339304913726 := by decide +kernel
private theorem range66From27261To3875 : Segment 66 27261 28052 0 3875 :=
  paid (pc:=71) (v:=339304913726) (by decide) source117_valid tests66_117_0 fee66_117_28052 (by decide +kernel)

private theorem tests66_111_3875 : ∀ z∈source111.plan.table,z.1.Valid 66 3875 := by decide +kernel
private theorem fee66_111_28052 :
    PopulationFees20258.bill (n:=28052) (PopulationFees20258.tabulate (28052-1) 256) source111.plan.table+
      4*28052*NaturalPopulation20258.weights source111.extras≤source111.plan.scale*389199228676 := by decide +kernel
private theorem range66From27261To4238 : Segment 66 27261 28052 3875 4238 :=
  paid (pc:=68) (v:=389199228676) (by decide) source111_valid tests66_111_3875 fee66_111_28052 (by decide +kernel)

private theorem tests66_112_4238 : ∀ z∈source112.plan.table,z.1.Valid 66 4238 := by decide +kernel
private theorem fee66_112_28052 :
    PopulationFees20258.bill (n:=28052) (PopulationFees20258.tabulate (28052-1) 256) source112.plan.table+
      4*28052*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*382234784185 := by decide +kernel
private theorem range66From27261To4291 : Segment 66 27261 28052 4238 4291 :=
  paid (pc:=68) (v:=382234784185) (by decide) source112_valid tests66_112_4238 fee66_112_28052 (by decide +kernel)

private theorem range66From27261 : Win 66 27261 28052 :=
  complete (by decide) (by decide) (join_population range66From27261To3875 (join_population range66From27261To4238 range66From27261To4291))

private theorem fee66_117_28781 :
    PopulationFees20258.bill (n:=28781) (PopulationFees20258.tabulate (28781-1) 256) source117.plan.table+
      4*28781*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*355637842071 := by decide +kernel
private theorem range66From28053To3919 : Segment 66 28053 28781 0 3919 :=
  paid (pc:=71) (v:=355637842071) (by decide) source117_valid tests66_117_0 fee66_117_28781 (by decide +kernel)

private theorem tests66_112_3919 : ∀ z∈source112.plan.table,z.1.Valid 66 3919 := by decide +kernel
private theorem fee66_112_28781 :
    PopulationFees20258.bill (n:=28781) (PopulationFees20258.tabulate (28781-1) 256) source112.plan.table+
      4*28781*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*400680804784 := by decide +kernel
private theorem range66From28053To4281 : Segment 66 28053 28781 3919 4281 :=
  paid (pc:=69) (v:=400680804784) (by decide) source112_valid tests66_112_3919 fee66_112_28781 (by decide +kernel)

private theorem tests66_112_4281 : ∀ z∈source112.plan.table,z.1.Valid 66 4281 := by decide +kernel
private theorem range66From28053To4291 : Segment 66 28053 28781 4281 4291 :=
  paid (pc:=69) (v:=400680804784) (by decide) source112_valid tests66_112_4281 fee66_112_28781 (by decide +kernel)

private theorem range66From28053 : Win 66 28053 28781 :=
  complete (by decide) (by decide) (join_population range66From28053To3919 (join_population range66From28053To4281 range66From28053To4291))

private theorem fee66_117_29476 :
    PopulationFees20258.bill (n:=29476) (PopulationFees20258.tabulate (29476-1) 256) source117.plan.table+
      4*29476*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*371738254818 := by decide +kernel
private theorem range66From28782To3954 : Segment 66 28782 29476 0 3954 :=
  paid (pc:=72) (v:=371738254818) (by decide) source117_valid tests66_117_0 fee66_117_29476 (by decide +kernel)

private theorem tests66_112_3954 : ∀ z∈source112.plan.table,z.1.Valid 66 3954 := by decide +kernel
private theorem fee66_112_29476 :
    PopulationFees20258.bill (n:=29476) (PopulationFees20258.tabulate (29476-1) 256) source112.plan.table+
      4*29476*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*419001181948 := by decide +kernel
private theorem range66From28782To4282 : Segment 66 28782 29476 3954 4282 :=
  paid (pc:=70) (v:=419001181948) (by decide) source112_valid tests66_112_3954 fee66_112_29476 (by decide +kernel)

private theorem tests66_112_4282 : ∀ z∈source112.plan.table,z.1.Valid 66 4282 := by decide +kernel
private theorem range66From28782To4291 : Segment 66 28782 29476 4282 4291 :=
  paid (pc:=70) (v:=419001181948) (by decide) source112_valid tests66_112_4282 fee66_112_29476 (by decide +kernel)

private theorem range66From28782 : Win 66 28782 29476 :=
  complete (by decide) (by decide) (join_population range66From28782To3954 (join_population range66From28782To4282 range66From28782To4291))

private theorem fee66_117_30160 :
    PopulationFees20258.bill (n:=30160) (PopulationFees20258.tabulate (30160-1) 256) source117.plan.table+
      4*30160*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*387852159191 := by decide +kernel
private theorem range66From29477To3982 : Segment 66 29477 30160 0 3982 :=
  paid (pc:=73) (v:=387852159191) (by decide) source117_valid tests66_117_0 fee66_117_30160 (by decide +kernel)

private theorem tests66_112_3982 : ∀ z∈source112.plan.table,z.1.Valid 66 3982 := by decide +kernel
private theorem fee66_112_30160 :
    PopulationFees20258.bill (n:=30160) (PopulationFees20258.tabulate (30160-1) 256) source112.plan.table+
      4*30160*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*437139171478 := by decide +kernel
private theorem range66From29477To4285 : Segment 66 29477 30160 3982 4285 :=
  paid (pc:=71) (v:=437139171478) (by decide) source112_valid tests66_112_3982 fee66_112_30160 (by decide +kernel)

private theorem tests66_112_4285 : ∀ z∈source112.plan.table,z.1.Valid 66 4285 := by decide +kernel
private theorem range66From29477To4291 : Segment 66 29477 30160 4285 4291 :=
  paid (pc:=71) (v:=437139171478) (by decide) source112_valid tests66_112_4285 fee66_112_30160 (by decide +kernel)

private theorem range66From29477 : Win 66 29477 30160 :=
  complete (by decide) (by decide) (join_population range66From29477To3982 (join_population range66From29477To4285 range66From29477To4291))

private theorem fee66_117_30856 :
    PopulationFees20258.bill (n:=30856) (PopulationFees20258.tabulate (30856-1) 256) source117.plan.table+
      4*30856*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*404459465960 := by decide +kernel
private theorem range66From30161To4006 : Segment 66 30161 30856 0 4006 :=
  paid (pc:=73) (v:=404459465960) (by decide) source117_valid tests66_117_0 fee66_117_30856 (by decide +kernel)

private theorem tests66_112_4006 : ∀ z∈source112.plan.table,z.1.Valid 66 4006 := by decide +kernel
private theorem fee66_112_30856 :
    PopulationFees20258.bill (n:=30856) (PopulationFees20258.tabulate (30856-1) 256) source112.plan.table+
      4*30856*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*456172687038 := by decide +kernel
private theorem range66From30161To4284 : Segment 66 30161 30856 4006 4284 :=
  paid (pc:=71) (v:=456172687038) (by decide) source112_valid tests66_112_4006 fee66_112_30856 (by decide +kernel)

private theorem tests66_112_4284 : ∀ z∈source112.plan.table,z.1.Valid 66 4284 := by decide +kernel
private theorem range66From30161To4291 : Segment 66 30161 30856 4284 4291 :=
  paid (pc:=71) (v:=456172687038) (by decide) source112_valid tests66_112_4284 fee66_112_30856 (by decide +kernel)

private theorem range66From30161 : Win 66 30161 30856 :=
  complete (by decide) (by decide) (join_population range66From30161To4006 (join_population range66From30161To4284 range66From30161To4291))

private theorem fee66_117_31579 :
    PopulationFees20258.bill (n:=31579) (PopulationFees20258.tabulate (31579-1) 256) source117.plan.table+
      4*31579*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*422172665147 := by decide +kernel
private theorem range66From30857To4027 : Segment 66 30857 31579 0 4027 :=
  paid (pc:=73) (v:=422172665147) (by decide) source117_valid tests66_117_0 fee66_117_31579 (by decide +kernel)

private theorem tests66_112_4027 : ∀ z∈source112.plan.table,z.1.Valid 66 4027 := by decide +kernel
private theorem fee66_112_31579 :
    PopulationFees20258.bill (n:=31579) (PopulationFees20258.tabulate (31579-1) 256) source112.plan.table+
      4*31579*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*476402050173 := by decide +kernel
private theorem range66From30857To4284 : Segment 66 30857 31579 4027 4284 :=
  paid (pc:=72) (v:=476402050173) (by decide) source112_valid tests66_112_4027 fee66_112_31579 (by decide +kernel)

private theorem range66From30857To4291 : Segment 66 30857 31579 4284 4291 :=
  paid (pc:=72) (v:=476402050173) (by decide) source112_valid tests66_112_4284 fee66_112_31579 (by decide +kernel)

private theorem range66From30857 : Win 66 30857 31579 :=
  complete (by decide) (by decide) (join_population range66From30857To4027 (join_population range66From30857To4284 range66From30857To4291))

private theorem fee66_117_32346 :
    PopulationFees20258.bill (n:=32346) (PopulationFees20258.tabulate (32346-1) 256) source117.plan.table+
      4*32346*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*441474789843 := by decide +kernel
private theorem range66From31580To4047 : Segment 66 31580 32346 0 4047 :=
  paid (pc:=74) (v:=441474789843) (by decide) source117_valid tests66_117_0 fee66_117_32346 (by decide +kernel)

private theorem tests66_112_4047 : ∀ z∈source112.plan.table,z.1.Valid 66 4047 := by decide +kernel
private theorem fee66_112_32346 :
    PopulationFees20258.bill (n:=32346) (PopulationFees20258.tabulate (32346-1) 256) source112.plan.table+
      4*32346*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*498182019755 := by decide +kernel
private theorem range66From31580To4286 : Segment 66 31580 32346 4047 4286 :=
  paid (pc:=72) (v:=498182019755) (by decide) source112_valid tests66_112_4047 fee66_112_32346 (by decide +kernel)

private theorem tests66_112_4286 : ∀ z∈source112.plan.table,z.1.Valid 66 4286 := by decide +kernel
private theorem range66From31580To4291 : Segment 66 31580 32346 4286 4291 :=
  paid (pc:=72) (v:=498182019755) (by decide) source112_valid tests66_112_4286 fee66_112_32346 (by decide +kernel)

private theorem range66From31580 : Win 66 31580 32346 :=
  complete (by decide) (by decide) (join_population range66From31580To4047 (join_population range66From31580To4286 range66From31580To4291))

private theorem fee66_117_33180 :
    PopulationFees20258.bill (n:=33180) (PopulationFees20258.tabulate (33180-1) 256) source117.plan.table+
      4*33180*NaturalPopulation20258.weights source117.extras≤source117.plan.scale*462924569327 := by decide +kernel
private theorem range66From32347To4065 : Segment 66 32347 33180 0 4065 :=
  paid (pc:=74) (v:=462924569327) (by decide) source117_valid tests66_117_0 fee66_117_33180 (by decide +kernel)

private theorem tests66_112_4065 : ∀ z∈source112.plan.table,z.1.Valid 66 4065 := by decide +kernel
private theorem fee66_112_33180 :
    PopulationFees20258.bill (n:=33180) (PopulationFees20258.tabulate (33180-1) 256) source112.plan.table+
      4*33180*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*522279577544 := by decide +kernel
private theorem range66From32347To4287 : Segment 66 32347 33180 4065 4287 :=
  paid (pc:=73) (v:=522279577544) (by decide) source112_valid tests66_112_4065 fee66_112_33180 (by decide +kernel)

private theorem tests66_112_4287 : ∀ z∈source112.plan.table,z.1.Valid 66 4287 := by decide +kernel
private theorem range66From32347To4291 : Segment 66 32347 33180 4287 4291 :=
  paid (pc:=73) (v:=522279577544) (by decide) source112_valid tests66_112_4287 fee66_112_33180 (by decide +kernel)

private theorem range66From32347 : Win 66 32347 33180 :=
  complete (by decide) (by decide) (join_population range66From32347To4065 (join_population range66From32347To4287 range66From32347To4291))

theorem cut66From27261 : Win 66 27261 33180 :=
  (join_ground (join_ground (join_ground range66From27261 range66From28053) (join_ground range66From28782 range66From29477)) (join_ground (join_ground range66From30161 range66From30857) (join_ground range66From31580 range66From32347)))

end JSP233.FiniteCutRanges20258
