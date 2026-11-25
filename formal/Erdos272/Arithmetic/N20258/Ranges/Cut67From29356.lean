module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source118
public import Erdos272.Arithmetic.N20258.Sources.Source119

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests67_118_0 : ∀ z∈source118.plan.table,z.1.Valid 67 0 := by decide +kernel
private theorem fee67_118_31056 :
    PopulationFees20258.bill (n:=31056) (PopulationFees20258.tabulate (31056-1) 256) source118.plan.table+
      4*31056*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*387066102283 := by decide +kernel
private theorem range67From29356To3623 : Segment 67 29356 31056 0 3623 :=
  paid (pc:=71) (v:=387066102283) (by decide) source118_valid tests67_118_0 fee67_118_31056 (by decide +kernel)

private theorem tests67_118_3623 : ∀ z∈source118.plan.table,z.1.Valid 67 3623 := by decide +kernel
private theorem range67From29356To3645 : Segment 67 29356 31056 3623 3645 :=
  paid (pc:=71) (v:=387066102283) (by decide) source118_valid tests67_118_3623 fee67_118_31056 (by decide +kernel)

private theorem tests67_118_3645 : ∀ z∈source118.plan.table,z.1.Valid 67 3645 := by decide +kernel
private theorem range67From29356To3647 : Segment 67 29356 31056 3645 3647 :=
  paid (pc:=71) (v:=387066102283) (by decide) source118_valid tests67_118_3645 fee67_118_31056 (by decide +kernel)

private theorem tests67_119_3647 : ∀ z∈source119.plan.table,z.1.Valid 67 3647 := by decide +kernel
private theorem fee67_119_31056 :
    PopulationFees20258.bill (n:=31056) (PopulationFees20258.tabulate (31056-1) 256) source119.plan.table+
      4*31056*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1028277863440 := by decide +kernel
private theorem range67From29356To4423 : Segment 67 29356 31056 3647 4423 :=
  paid (pc:=65) (v:=1028277863440) (by decide) source119_valid tests67_119_3647 fee67_119_31056 (by decide +kernel)

private theorem range67From29356 : Win 67 29356 31056 :=
  complete (by decide) (by decide) (join_population (join_population range67From29356To3623 range67From29356To3645) (join_population range67From29356To3647 range67From29356To4423))

private theorem fee67_118_33004 :
    PopulationFees20258.bill (n:=33004) (PopulationFees20258.tabulate (33004-1) 256) source118.plan.table+
      4*33004*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*433439615243 := by decide +kernel
private theorem range67From31057To3628 : Segment 67 31057 33004 0 3628 :=
  paid (pc:=72) (v:=433439615243) (by decide) source118_valid tests67_118_0 fee67_118_33004 (by decide +kernel)

private theorem tests67_118_3628 : ∀ z∈source118.plan.table,z.1.Valid 67 3628 := by decide +kernel
private theorem range67From31057To3645 : Segment 67 31057 33004 3628 3645 :=
  paid (pc:=72) (v:=433439615243) (by decide) source118_valid tests67_118_3628 fee67_118_33004 (by decide +kernel)

private theorem range67From31057To3647 : Segment 67 31057 33004 3645 3647 :=
  paid (pc:=72) (v:=433439615243) (by decide) source118_valid tests67_118_3645 fee67_118_33004 (by decide +kernel)

private theorem fee67_119_33004 :
    PopulationFees20258.bill (n:=33004) (PopulationFees20258.tabulate (33004-1) 256) source119.plan.table+
      4*33004*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1147143571172 := by decide +kernel
private theorem range67From31057To4423 : Segment 67 31057 33004 3647 4423 :=
  paid (pc:=67) (v:=1147143571172) (by decide) source119_valid tests67_119_3647 fee67_119_33004 (by decide +kernel)

private theorem range67From31057 : Win 67 31057 33004 :=
  complete (by decide) (by decide) (join_population (join_population range67From31057To3628 range67From31057To3645) (join_population range67From31057To3647 range67From31057To4423))

private theorem fee67_118_34924 :
    PopulationFees20258.bill (n:=34924) (PopulationFees20258.tabulate (34924-1) 256) source118.plan.table+
      4*34924*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*481757062315 := by decide +kernel
private theorem range67From33005To3772 : Segment 67 33005 34924 0 3772 :=
  paid (pc:=73) (v:=481757062315) (by decide) source118_valid tests67_118_0 fee67_118_34924 (by decide +kernel)

private theorem tests67_119_3772 : ∀ z∈source119.plan.table,z.1.Valid 67 3772 := by decide +kernel
private theorem fee67_119_34924 :
    PopulationFees20258.bill (n:=34924) (PopulationFees20258.tabulate (34924-1) 256) source119.plan.table+
      4*34924*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1270630624383 := by decide +kernel
private theorem range67From33005To4395 : Segment 67 33005 34924 3772 4395 :=
  paid (pc:=69) (v:=1270630624383) (by decide) source119_valid tests67_119_3772 fee67_119_34924 (by decide +kernel)

private theorem tests67_119_4395 : ∀ z∈source119.plan.table,z.1.Valid 67 4395 := by decide +kernel
private theorem range67From33005To4423 : Segment 67 33005 34924 4395 4423 :=
  paid (pc:=69) (v:=1270630624383) (by decide) source119_valid tests67_119_4395 fee67_119_34924 (by decide +kernel)

private theorem range67From33005 : Win 67 33005 34924 :=
  complete (by decide) (by decide) (join_population range67From33005To3772 (join_population range67From33005To4395 range67From33005To4423))

private theorem fee67_118_36822 :
    PopulationFees20258.bill (n:=36822) (PopulationFees20258.tabulate (36822-1) 256) source118.plan.table+
      4*36822*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*531854417931 := by decide +kernel
private theorem range67From34925To3919 : Segment 67 34925 36822 0 3919 :=
  paid (pc:=73) (v:=531854417931) (by decide) source118_valid tests67_118_0 fee67_118_36822 (by decide +kernel)

private theorem tests67_119_3919 : ∀ z∈source119.plan.table,z.1.Valid 67 3919 := by decide +kernel
private theorem fee67_119_36822 :
    PopulationFees20258.bill (n:=36822) (PopulationFees20258.tabulate (36822-1) 256) source119.plan.table+
      4*36822*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1398580260891 := by decide +kernel
private theorem range67From34925To4406 : Segment 67 34925 36822 3919 4406 :=
  paid (pc:=71) (v:=1398580260891) (by decide) source119_valid tests67_119_3919 fee67_119_36822 (by decide +kernel)

private theorem tests67_119_4406 : ∀ z∈source119.plan.table,z.1.Valid 67 4406 := by decide +kernel
private theorem range67From34925To4423 : Segment 67 34925 36822 4406 4423 :=
  paid (pc:=71) (v:=1398580260891) (by decide) source119_valid tests67_119_4406 fee67_119_36822 (by decide +kernel)

private theorem range67From34925 : Win 67 34925 36822 :=
  complete (by decide) (by decide) (join_population range67From34925To3919 (join_population range67From34925To4406 range67From34925To4423))

private theorem fee67_118_38808 :
    PopulationFees20258.bill (n:=38808) (PopulationFees20258.tabulate (38808-1) 256) source118.plan.table+
      4*38808*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*586951127271 := by decide +kernel
private theorem range67From36823To4037 : Segment 67 36823 38808 0 4037 :=
  paid (pc:=74) (v:=586951127271) (by decide) source118_valid tests67_118_0 fee67_118_38808 (by decide +kernel)

private theorem tests67_119_4037 : ∀ z∈source119.plan.table,z.1.Valid 67 4037 := by decide +kernel
private theorem fee67_119_38808 :
    PopulationFees20258.bill (n:=38808) (PopulationFees20258.tabulate (38808-1) 256) source119.plan.table+
      4*38808*NaturalPopulation20258.weights source119.extras≤source119.plan.scale*1538953420332 := by decide +kernel
private theorem range67From36823To4413 : Segment 67 36823 38808 4037 4413 :=
  paid (pc:=72) (v:=1538953420332) (by decide) source119_valid tests67_119_4037 fee67_119_38808 (by decide +kernel)

private theorem tests67_119_4413 : ∀ z∈source119.plan.table,z.1.Valid 67 4413 := by decide +kernel
private theorem range67From36823To4423 : Segment 67 36823 38808 4413 4423 :=
  paid (pc:=72) (v:=1538953420332) (by decide) source119_valid tests67_119_4413 fee67_119_38808 (by decide +kernel)

private theorem range67From36823 : Win 67 36823 38808 :=
  complete (by decide) (by decide) (join_population range67From36823To4037 (join_population range67From36823To4413 range67From36823To4423))

private theorem fee67_118_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source118.plan.table+
      4*39999*NaturalPopulation20258.weights source118.extras≤source118.plan.scale*621458351503 := by decide +kernel
private theorem range67From38809To4423 : Segment 67 38809 39999 0 4423 :=
  paid (pc:=76) (v:=621458351503) (by decide) source118_valid tests67_118_0 fee67_118_39999 (by decide +kernel)

private theorem range67From38809 : Win 67 38809 39999 :=
  complete (by decide) (by decide) range67From38809To4423

theorem cut67From29356 : Win 67 29356 39999 :=
  (join_ground (join_ground range67From29356 (join_ground range67From31057 range67From33005)) (join_ground range67From34925 (join_ground range67From36823 range67From38809)))

end JSP233.FiniteCutRanges20258
