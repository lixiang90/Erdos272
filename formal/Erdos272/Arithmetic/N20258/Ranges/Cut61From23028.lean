module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source103
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source109

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests61_107_0 : ∀ z∈source107.plan.table,z.1.Valid 61 0 := by decide +kernel
private theorem fee61_107_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source107.plan.table+
      4*23780*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*237526086713 := by decide +kernel
private theorem range61From23028To2975 : Segment 61 23028 23780 0 2975 :=
  paid (pc:=73) (v:=237526086713) (by decide) source107_valid tests61_107_0 fee61_107_23780 (by decide +kernel)

private theorem tests61_107_2975 : ∀ z∈source107.plan.table,z.1.Valid 61 2975 := by decide +kernel
private theorem range61From23028To3001 : Segment 61 23028 23780 2975 3001 :=
  paid (pc:=72) (v:=237526086713) (by decide) source107_valid tests61_107_2975 fee61_107_23780 (by decide +kernel)

private theorem tests61_107_3001 : ∀ z∈source107.plan.table,z.1.Valid 61 3001 := by decide +kernel
private theorem range61From23028To3003 : Segment 61 23028 23780 3001 3003 :=
  paid (pc:=72) (v:=237526086713) (by decide) source107_valid tests61_107_3001 fee61_107_23780 (by decide +kernel)

private theorem tests61_103_3003 : ∀ z∈source103.plan.table,z.1.Valid 61 3003 := by decide +kernel
private theorem fee61_103_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source103.plan.table+
      4*23780*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*299139580582 := by decide +kernel
private theorem range61From23028To3060 : Segment 61 23028 23780 3003 3060 :=
  paid (pc:=72) (v:=299139580582) (by decide) source103_valid tests61_103_3003 fee61_103_23780 (by decide +kernel)

private theorem tests61_102_3060 : ∀ z∈source102.plan.table,z.1.Valid 61 3060 := by decide +kernel
private theorem fee61_102_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source102.plan.table+
      4*23780*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*292733295460 := by decide +kernel
private theorem range61From23028To3104 : Segment 61 23028 23780 3060 3104 :=
  paid (pc:=72) (v:=292733295460) (by decide) source102_valid tests61_102_3060 fee61_102_23780 (by decide +kernel)

private theorem tests61_106_3104 : ∀ z∈source106.plan.table,z.1.Valid 61 3104 := by decide +kernel
private theorem fee61_106_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source106.plan.table+
      4*23780*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*333976210934 := by decide +kernel
private theorem range61From23028To3381 : Segment 61 23028 23780 3104 3381 :=
  paid (pc:=69) (v:=333976210934) (by decide) source106_valid tests61_106_3104 fee61_106_23780 (by decide +kernel)

private theorem tests61_105_3381 : ∀ z∈source105.plan.table,z.1.Valid 61 3381 := by decide +kernel
private theorem fee61_105_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source105.plan.table+
      4*23780*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*327431190487 := by decide +kernel
private theorem range61From23028To3456 : Segment 61 23028 23780 3381 3456 :=
  paid (pc:=69) (v:=327431190487) (by decide) source105_valid tests61_105_3381 fee61_105_23780 (by decide +kernel)

private theorem tests61_109_3456 : ∀ z∈source109.plan.table,z.1.Valid 61 3456 := by decide +kernel
private theorem fee61_109_23780 :
    PopulationFees20258.bill (n:=23780) (PopulationFees20258.tabulate (23780-1) 256) source109.plan.table+
      4*23780*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*267160884552 := by decide +kernel
private theorem range61From23028To3661 : Segment 61 23028 23780 3456 3661 :=
  paid (pc:=66) (v:=267160884552) (by decide) source109_valid tests61_109_3456 fee61_109_23780 (by decide +kernel)

private theorem range61From23028 : Win 61 23028 23780 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range61From23028To2975 range61From23028To3001) (join_population range61From23028To3003 range61From23028To3060)) (join_population (join_population range61From23028To3104 range61From23028To3381) (join_population range61From23028To3456 range61From23028To3661)))

private theorem fee61_107_24536 :
    PopulationFees20258.bill (n:=24536) (PopulationFees20258.tabulate (24536-1) 256) source107.plan.table+
      4*24536*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*251395847691 := by decide +kernel
private theorem range61From23781To3011 : Segment 61 23781 24536 0 3011 :=
  paid (pc:=73) (v:=251395847691) (by decide) source107_valid tests61_107_0 fee61_107_24536 (by decide +kernel)

private theorem tests61_103_3011 : ∀ z∈source103.plan.table,z.1.Valid 61 3011 := by decide +kernel
private theorem fee61_103_24536 :
    PopulationFees20258.bill (n:=24536) (PopulationFees20258.tabulate (24536-1) 256) source103.plan.table+
      4*24536*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*316728175574 := by decide +kernel
private theorem range61From23781To3081 : Segment 61 23781 24536 3011 3081 :=
  paid (pc:=73) (v:=316728175574) (by decide) source103_valid tests61_103_3011 fee61_103_24536 (by decide +kernel)

private theorem tests61_106_3081 : ∀ z∈source106.plan.table,z.1.Valid 61 3081 := by decide +kernel
private theorem fee61_106_24536 :
    PopulationFees20258.bill (n:=24536) (PopulationFees20258.tabulate (24536-1) 256) source106.plan.table+
      4*24536*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*353741568061 := by decide +kernel
private theorem range61From23781To3354 : Segment 61 23781 24536 3081 3354 :=
  paid (pc:=71) (v:=353741568061) (by decide) source106_valid tests61_106_3081 fee61_106_24536 (by decide +kernel)

private theorem tests61_105_3354 : ∀ z∈source105.plan.table,z.1.Valid 61 3354 := by decide +kernel
private theorem fee61_105_24536 :
    PopulationFees20258.bill (n:=24536) (PopulationFees20258.tabulate (24536-1) 256) source105.plan.table+
      4*24536*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*346843970120 := by decide +kernel
private theorem range61From23781To3417 : Segment 61 23781 24536 3354 3417 :=
  paid (pc:=70) (v:=346843970120) (by decide) source105_valid tests61_105_3354 fee61_105_24536 (by decide +kernel)

private theorem tests61_105_3417 : ∀ z∈source105.plan.table,z.1.Valid 61 3417 := by decide +kernel
private theorem range61From23781To3419 : Segment 61 23781 24536 3417 3419 :=
  paid (pc:=70) (v:=346843970120) (by decide) source105_valid tests61_105_3417 fee61_105_24536 (by decide +kernel)

private theorem tests61_108_3419 : ∀ z∈source108.plan.table,z.1.Valid 61 3419 := by decide +kernel
private theorem fee61_108_24536 :
    PopulationFees20258.bill (n:=24536) (PopulationFees20258.tabulate (24536-1) 256) source108.plan.table+
      4*24536*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*285661835643 := by decide +kernel
private theorem range61From23781To3661 : Segment 61 23781 24536 3419 3661 :=
  paid (pc:=67) (v:=285661835643) (by decide) source108_valid tests61_108_3419 fee61_108_24536 (by decide +kernel)

private theorem range61From23781 : Win 61 23781 24536 :=
  complete (by decide) (by decide) (join_population (join_population range61From23781To3011 (join_population range61From23781To3081 range61From23781To3354)) (join_population range61From23781To3417 (join_population range61From23781To3419 range61From23781To3661)))

private theorem fee61_107_25282 :
    PopulationFees20258.bill (n:=25282) (PopulationFees20258.tabulate (25282-1) 256) source107.plan.table+
      4*25282*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*265609498558 := by decide +kernel
private theorem range61From24537To3056 : Segment 61 24537 25282 0 3056 :=
  paid (pc:=74) (v:=265609498558) (by decide) source107_valid tests61_107_0 fee61_107_25282 (by decide +kernel)

private theorem tests61_102_3056 : ∀ z∈source102.plan.table,z.1.Valid 61 3056 := by decide +kernel
private theorem fee61_102_25282 :
    PopulationFees20258.bill (n:=25282) (PopulationFees20258.tabulate (25282-1) 256) source102.plan.table+
      4*25282*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*327215155464 := by decide +kernel
private theorem range61From24537To3155 : Segment 61 24537 25282 3056 3155 :=
  paid (pc:=73) (v:=327215155464) (by decide) source102_valid tests61_102_3056 fee61_102_25282 (by decide +kernel)

private theorem tests61_105_3155 : ∀ z∈source105.plan.table,z.1.Valid 61 3155 := by decide +kernel
private theorem fee61_105_25282 :
    PopulationFees20258.bill (n:=25282) (PopulationFees20258.tabulate (25282-1) 256) source105.plan.table+
      4*25282*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*365913914614 := by decide +kernel
private theorem range61From24537To3411 : Segment 61 24537 25282 3155 3411 :=
  paid (pc:=71) (v:=365913914614) (by decide) source105_valid tests61_105_3155 fee61_105_25282 (by decide +kernel)

private theorem tests61_105_3411 : ∀ z∈source105.plan.table,z.1.Valid 61 3411 := by decide +kernel
private theorem range61From24537To3419 : Segment 61 24537 25282 3411 3419 :=
  paid (pc:=71) (v:=365913914614) (by decide) source105_valid tests61_105_3411 fee61_105_25282 (by decide +kernel)

private theorem fee61_108_25282 :
    PopulationFees20258.bill (n:=25282) (PopulationFees20258.tabulate (25282-1) 256) source108.plan.table+
      4*25282*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*301821460577 := by decide +kernel
private theorem range61From24537To3661 : Segment 61 24537 25282 3419 3661 :=
  paid (pc:=69) (v:=301821460577) (by decide) source108_valid tests61_108_3419 fee61_108_25282 (by decide +kernel)

private theorem range61From24537 : Win 61 24537 25282 :=
  complete (by decide) (by decide) (join_population (join_population range61From24537To3056 range61From24537To3155) (join_population range61From24537To3411 (join_population range61From24537To3419 range61From24537To3661)))

private theorem fee61_107_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source107.plan.table+
      4*26040*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*280364685597 := by decide +kernel
private theorem range61From25283To3098 : Segment 61 25283 26040 0 3098 :=
  paid (pc:=74) (v:=280364685597) (by decide) source107_valid tests61_107_0 fee61_107_26040 (by decide +kernel)

private theorem tests61_106_3098 : ∀ z∈source106.plan.table,z.1.Valid 61 3098 := by decide +kernel
private theorem fee61_106_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source106.plan.table+
      4*26040*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*393811781539 := by decide +kernel
private theorem range61From25283To3367 : Segment 61 25283 26040 3098 3367 :=
  paid (pc:=72) (v:=393811781539) (by decide) source106_valid tests61_106_3098 fee61_106_26040 (by decide +kernel)

private theorem tests61_105_3367 : ∀ z∈source105.plan.table,z.1.Valid 61 3367 := by decide +kernel
private theorem fee61_105_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source105.plan.table+
      4*26040*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*386164015031 := by decide +kernel
private theorem range61From25283To3420 : Segment 61 25283 26040 3367 3420 :=
  paid (pc:=72) (v:=386164015031) (by decide) source105_valid tests61_105_3367 fee61_105_26040 (by decide +kernel)

private theorem tests61_108_3420 : ∀ z∈source108.plan.table,z.1.Valid 61 3420 := by decide +kernel
private theorem fee61_108_26040 :
    PopulationFees20258.bill (n:=26040) (PopulationFees20258.tabulate (26040-1) 256) source108.plan.table+
      4*26040*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*318633361830 := by decide +kernel
private theorem range61From25283To3661 : Segment 61 25283 26040 3420 3661 :=
  paid (pc:=70) (v:=318633361830) (by decide) source108_valid tests61_108_3420 fee61_108_26040 (by decide +kernel)

private theorem range61From25283 : Win 61 25283 26040 :=
  complete (by decide) (by decide) (join_population (join_population range61From25283To3098 range61From25283To3367) (join_population range61From25283To3420 range61From25283To3661))

theorem cut61From23028 : Win 61 23028 26040 :=
  (join_ground (join_ground range61From23028 range61From23781) (join_ground range61From24537 range61From25283))

end JSP233.FiniteCutRanges20258
