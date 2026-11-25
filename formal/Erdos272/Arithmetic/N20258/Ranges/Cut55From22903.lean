module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source077
public import Erdos272.Arithmetic.N20258.Sources.Source078
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086
public import Erdos272.Arithmetic.N20258.Sources.Source087

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source082.plan.table+
      4*23360*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*161498728125 := by decide +kernel
private theorem range55From22903To2529 : Segment 55 22903 23360 0 2529 :=
  paid (pc:=77) (v:=161498728125) (by decide) source082_valid tests55_082_0 fee55_082_23360 (by decide +kernel)

private theorem tests55_077_2529 : ∀ z∈source077.plan.table,z.1.Valid 55 2529 := by decide +kernel
private theorem fee55_077_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source077.plan.table+
      4*23360*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*257563268812 := by decide +kernel
private theorem range55From22903To2635 : Segment 55 22903 23360 2529 2635 :=
  paid (pc:=77) (v:=257563268812) (by decide) source077_valid tests55_077_2529 fee55_077_23360 (by decide +kernel)

private theorem tests55_086_2635 : ∀ z∈source086.plan.table,z.1.Valid 55 2635 := by decide +kernel
private theorem fee55_086_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source086.plan.table+
      4*23360*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*306543067295 := by decide +kernel
private theorem range55From22903To2700 : Segment 55 22903 23360 2635 2700 :=
  paid (pc:=76) (v:=306543067295) (by decide) source086_valid tests55_086_2635 fee55_086_23360 (by decide +kernel)

private theorem tests55_085_2700 : ∀ z∈source085.plan.table,z.1.Valid 55 2700 := by decide +kernel
private theorem fee55_085_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source085.plan.table+
      4*23360*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*283309958019 := by decide +kernel
private theorem range55From22903To2831 : Segment 55 22903 23360 2700 2831 :=
  paid (pc:=75) (v:=283309958019) (by decide) source085_valid tests55_085_2700 fee55_085_23360 (by decide +kernel)

private theorem tests55_087_2831 : ∀ z∈source087.plan.table,z.1.Valid 55 2831 := by decide +kernel
private theorem fee55_087_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source087.plan.table+
      4*23360*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*263084473580 := by decide +kernel
private theorem range55From22903To2952 : Segment 55 22903 23360 2831 2952 :=
  paid (pc:=74) (v:=263084473580) (by decide) source087_valid tests55_087_2831 fee55_087_23360 (by decide +kernel)

private theorem tests55_080_2952 : ∀ z∈source080.plan.table,z.1.Valid 55 2952 := by decide +kernel
private theorem fee55_080_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source080.plan.table+
      4*23360*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*260355982943 := by decide +kernel
private theorem range55From22903To2971 : Segment 55 22903 23360 2952 2971 :=
  paid (pc:=74) (v:=260355982943) (by decide) source080_valid tests55_080_2952 fee55_080_23360 (by decide +kernel)

private theorem range55From22903 : Win 55 22903 23360 :=
  complete (by decide) (by decide) (join_population (join_population range55From22903To2529 (join_population range55From22903To2635 range55From22903To2700)) (join_population range55From22903To2831 (join_population range55From22903To2952 range55From22903To2971)))

private theorem fee55_082_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source082.plan.table+
      4*23863*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*168019780746 := by decide +kernel
private theorem range55From23361To2553 : Segment 55 23361 23863 0 2553 :=
  paid (pc:=77) (v:=168019780746) (by decide) source082_valid tests55_082_0 fee55_082_23863 (by decide +kernel)

private theorem tests55_077_2553 : ∀ z∈source077.plan.table,z.1.Valid 55 2553 := by decide +kernel
private theorem fee55_077_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source077.plan.table+
      4*23863*NaturalPopulation20258.weights source077.extras≤source077.plan.scale*267738728572 := by decide +kernel
private theorem range55From23361To2652 : Segment 55 23361 23863 2553 2652 :=
  paid (pc:=77) (v:=267738728572) (by decide) source077_valid tests55_077_2553 fee55_077_23863 (by decide +kernel)

private theorem tests55_078_2652 : ∀ z∈source078.plan.table,z.1.Valid 55 2652 := by decide +kernel
private theorem fee55_078_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source078.plan.table+
      4*23863*NaturalPopulation20258.weights source078.extras≤source078.plan.scale*249908809452 := by decide +kernel
private theorem range55From23361To2736 : Segment 55 23361 23863 2652 2736 :=
  paid (pc:=76) (v:=249908809452) (by decide) source078_valid tests55_078_2652 fee55_078_23863 (by decide +kernel)

private theorem tests55_085_2736 : ∀ z∈source085.plan.table,z.1.Valid 55 2736 := by decide +kernel
private theorem fee55_085_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source085.plan.table+
      4*23863*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*294581230599 := by decide +kernel
private theorem range55From23361To2837 : Segment 55 23361 23863 2736 2837 :=
  paid (pc:=75) (v:=294581230599) (by decide) source085_valid tests55_085_2736 fee55_085_23863 (by decide +kernel)

private theorem tests55_087_2837 : ∀ z∈source087.plan.table,z.1.Valid 55 2837 := by decide +kernel
private theorem fee55_087_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source087.plan.table+
      4*23863*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*273585589877 := by decide +kernel
private theorem range55From23361To2952 : Segment 55 23361 23863 2837 2952 :=
  paid (pc:=74) (v:=273585589877) (by decide) source087_valid tests55_087_2837 fee55_087_23863 (by decide +kernel)

private theorem fee55_080_23863 :
    PopulationFees20258.bill (n:=23863) (PopulationFees20258.tabulate (23863-1) 256) source080.plan.table+
      4*23863*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*270736614205 := by decide +kernel
private theorem range55From23361To2971 : Segment 55 23361 23863 2952 2971 :=
  paid (pc:=74) (v:=270736614205) (by decide) source080_valid tests55_080_2952 fee55_080_23863 (by decide +kernel)

private theorem range55From23361 : Win 55 23361 23863 :=
  complete (by decide) (by decide) (join_population (join_population range55From23361To2553 (join_population range55From23361To2652 range55From23361To2736)) (join_population range55From23361To2837 (join_population range55From23361To2952 range55From23361To2971)))

private theorem fee55_082_24420 :
    PopulationFees20258.bill (n:=24420) (PopulationFees20258.tabulate (24420-1) 256) source082.plan.table+
      4*24420*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*175350427853 := by decide +kernel
private theorem range55From23864To2577 : Segment 55 23864 24420 0 2577 :=
  paid (pc:=77) (v:=175350427853) (by decide) source082_valid tests55_082_0 fee55_082_24420 (by decide +kernel)

private theorem tests55_086_2577 : ∀ z∈source086.plan.table,z.1.Valid 55 2577 := by decide +kernel
private theorem fee55_086_24420 :
    PopulationFees20258.bill (n:=24420) (PopulationFees20258.tabulate (24420-1) 256) source086.plan.table+
      4*24420*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*332361475544 := by decide +kernel
private theorem range55From23864To2720 : Segment 55 23864 24420 2577 2720 :=
  paid (pc:=76) (v:=332361475544) (by decide) source086_valid tests55_086_2577 fee55_086_24420 (by decide +kernel)

private theorem tests55_085_2720 : ∀ z∈source085.plan.table,z.1.Valid 55 2720 := by decide +kernel
private theorem fee55_085_24420 :
    PopulationFees20258.bill (n:=24420) (PopulationFees20258.tabulate (24420-1) 256) source085.plan.table+
      4*24420*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*307252706079 := by decide +kernel
private theorem range55From23864To2844 : Segment 55 23864 24420 2720 2844 :=
  paid (pc:=76) (v:=307252706079) (by decide) source085_valid tests55_085_2720 fee55_085_24420 (by decide +kernel)

private theorem tests55_080_2844 : ∀ z∈source080.plan.table,z.1.Valid 55 2844 := by decide +kernel
private theorem fee55_080_24420 :
    PopulationFees20258.bill (n:=24420) (PopulationFees20258.tabulate (24420-1) 256) source080.plan.table+
      4*24420*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*282630610571 := by decide +kernel
private theorem range55From23864To2969 : Segment 55 23864 24420 2844 2969 :=
  paid (pc:=75) (v:=282630610571) (by decide) source080_valid tests55_080_2844 fee55_080_24420 (by decide +kernel)

private theorem tests55_080_2969 : ∀ z∈source080.plan.table,z.1.Valid 55 2969 := by decide +kernel
private theorem range55From23864To2971 : Segment 55 23864 24420 2969 2971 :=
  paid (pc:=75) (v:=282630610571) (by decide) source080_valid tests55_080_2969 fee55_080_24420 (by decide +kernel)

private theorem range55From23864 : Win 55 23864 24420 :=
  complete (by decide) (by decide) (join_population (join_population range55From23864To2577 range55From23864To2720) (join_population range55From23864To2844 (join_population range55From23864To2969 range55From23864To2971)))

private theorem fee55_082_25050 :
    PopulationFees20258.bill (n:=25050) (PopulationFees20258.tabulate (25050-1) 256) source082.plan.table+
      4*25050*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*183896908129 := by decide +kernel
private theorem range55From24421To2602 : Segment 55 24421 25050 0 2602 :=
  paid (pc:=77) (v:=183896908129) (by decide) source082_valid tests55_082_0 fee55_082_25050 (by decide +kernel)

private theorem tests55_086_2602 : ∀ z∈source086.plan.table,z.1.Valid 55 2602 := by decide +kernel
private theorem fee55_086_25050 :
    PopulationFees20258.bill (n:=25050) (PopulationFees20258.tabulate (25050-1) 256) source086.plan.table+
      4*25050*NaturalPopulation20258.weights source086.extras≤source086.plan.scale*348257490748 := by decide +kernel
private theorem range55From24421To2731 : Segment 55 24421 25050 2602 2731 :=
  paid (pc:=77) (v:=348257490748) (by decide) source086_valid tests55_086_2602 fee55_086_25050 (by decide +kernel)

private theorem tests55_085_2731 : ∀ z∈source085.plan.table,z.1.Valid 55 2731 := by decide +kernel
private theorem fee55_085_25050 :
    PopulationFees20258.bill (n:=25050) (PopulationFees20258.tabulate (25050-1) 256) source085.plan.table+
      4*25050*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*321993110997 := by decide +kernel
private theorem range55From24421To2849 : Segment 55 24421 25050 2731 2849 :=
  paid (pc:=76) (v:=321993110997) (by decide) source085_valid tests55_085_2731 fee55_085_25050 (by decide +kernel)

private theorem tests55_080_2849 : ∀ z∈source080.plan.table,z.1.Valid 55 2849 := by decide +kernel
private theorem fee55_080_25050 :
    PopulationFees20258.bill (n:=25050) (PopulationFees20258.tabulate (25050-1) 256) source080.plan.table+
      4*25050*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*296267791077 := by decide +kernel
private theorem range55From24421To2968 : Segment 55 24421 25050 2849 2968 :=
  paid (pc:=75) (v:=296267791077) (by decide) source080_valid tests55_080_2849 fee55_080_25050 (by decide +kernel)

private theorem tests55_080_2968 : ∀ z∈source080.plan.table,z.1.Valid 55 2968 := by decide +kernel
private theorem range55From24421To2971 : Segment 55 24421 25050 2968 2971 :=
  paid (pc:=75) (v:=296267791077) (by decide) source080_valid tests55_080_2968 fee55_080_25050 (by decide +kernel)

private theorem range55From24421 : Win 55 24421 25050 :=
  complete (by decide) (by decide) (join_population (join_population range55From24421To2602 range55From24421To2731) (join_population range55From24421To2849 (join_population range55From24421To2968 range55From24421To2971)))

theorem cut55From22903 : Win 55 22903 25050 :=
  (join_ground (join_ground range55From22903 range55From23361) (join_ground range55From23864 range55From24421))

end JSP233.FiniteCutRanges20258
