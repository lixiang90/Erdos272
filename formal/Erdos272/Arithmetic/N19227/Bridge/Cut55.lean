module

public import Erdos272.Arithmetic.N19227.Sources.P123
public import Erdos272.Arithmetic.N20258.Sources.Source075
public import Erdos272.Arithmetic.N20258.Sources.Source081
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source083
public import Erdos272.Arithmetic.N20258.Sources.Source084
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source086
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee66At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source082.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source082.extras≤PopulationSources20258.source082.plan.scale*119683757293 := by decide +kernel
private theorem from19683To2375 : Segment 55 19683 19865 0 2375 :=
  paid (pc:=77) (v:=119683757293) (by decide) PopulationSources20258.source082_valid (by decide +kernel) fee66At19865 (by decide +kernel)

private theorem fee123At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) JSP233.Credit19227.p123.plan.table+
      4*19865*NaturalPopulation20258.weights JSP233.Credit19227.p123.extras≤JSP233.Credit19227.p123.plan.scale*165669479134 := by decide +kernel
private theorem from19683To2393 : Segment 55 19683 19865 2375 2393 :=
  paid (pc:=77) (v:=165669479134) (by decide) JSP233.Credit19227.p123_valid (by decide +kernel) fee123At19865 (by decide +kernel)

private theorem fee61At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source075.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source075.extras≤PopulationSources20258.source075.plan.scale*161312606474 := by decide +kernel
private theorem from19683To2425 : Segment 55 19683 19865 2393 2425 :=
  paid (pc:=76) (v:=161312606474) (by decide) PopulationSources20258.source075_valid (by decide +kernel) fee61At19865 (by decide +kernel)

private theorem fee67At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source084.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source084.extras≤PopulationSources20258.source084.plan.scale*198520402668 := by decide +kernel
private theorem from19683To2506 : Segment 55 19683 19865 2425 2506 :=
  paid (pc:=76) (v:=198520402668) (by decide) PopulationSources20258.source084_valid (by decide +kernel) fee67At19865 (by decide +kernel)

private theorem fee68At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source083.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source083.extras≤PopulationSources20258.source083.plan.scale*191733723647 := by decide +kernel
private theorem from19683To2567 : Segment 55 19683 19865 2506 2567 :=
  paid (pc:=75) (v:=191733723647) (by decide) PopulationSources20258.source083_valid (by decide +kernel) fee68At19865 (by decide +kernel)

private theorem fee69At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source086.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source086.extras≤PopulationSources20258.source086.plan.scale*228475909867 := by decide +kernel
private theorem from19683To2707 : Segment 55 19683 19865 2567 2707 :=
  paid (pc:=74) (v:=228475909867) (by decide) PopulationSources20258.source086_valid (by decide +kernel) fee69At19865 (by decide +kernel)

private theorem fee70At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source085.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source085.extras≤PopulationSources20258.source085.plan.scale*210955603221 := by decide +kernel
private theorem from19683To2911 : Segment 55 19683 19865 2707 2911 :=
  paid (pc:=72) (v:=210955603221) (by decide) PopulationSources20258.source085_valid (by decide +kernel) fee70At19865 (by decide +kernel)

private theorem fee65At19865 :
    PopulationFees20258.bill (n:=19865) (PopulationFees20258.tabulate (19865-1) 256) PopulationSources20258.source081.plan.table+
      4*19865*NaturalPopulation20258.weights PopulationSources20258.source081.extras≤PopulationSources20258.source081.plan.scale*256001323048 := by decide +kernel
private theorem from19683To2971 : Segment 55 19683 19865 2911 2971 :=
  paid (pc:=65) (v:=256001323048) (by decide) PopulationSources20258.source081_valid (by decide +kernel) fee65At19865 (by decide +kernel)

private theorem range19683 : Win 55 19683 19865 :=
  complete (by decide) (by decide) (join_population (join_population (join_population from19683To2375 from19683To2393) (join_population from19683To2425 from19683To2506)) (join_population (join_population from19683To2567 from19683To2707) (join_population from19683To2911 from19683To2971)))

private theorem fee66At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source082.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source082.extras≤PopulationSources20258.source082.plan.scale*121952173289 := by decide +kernel
private theorem from19866To2382 : Segment 55 19866 20068 0 2382 :=
  paid (pc:=77) (v:=121952173289) (by decide) PopulationSources20258.source082_valid (by decide +kernel) fee66At20068 (by decide +kernel)

private theorem fee61At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source075.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source075.extras≤PopulationSources20258.source075.plan.scale*164268807661 := by decide +kernel
private theorem from19866To2428 : Segment 55 19866 20068 2382 2428 :=
  paid (pc:=76) (v:=164268807661) (by decide) PopulationSources20258.source075_valid (by decide +kernel) fee61At20068 (by decide +kernel)

private theorem fee67At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source084.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source084.extras≤PopulationSources20258.source084.plan.scale*202234368177 := by decide +kernel
private theorem from19866To2505 : Segment 55 19866 20068 2428 2505 :=
  paid (pc:=76) (v:=202234368177) (by decide) PopulationSources20258.source084_valid (by decide +kernel) fee67At20068 (by decide +kernel)

private theorem fee68At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source083.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source083.extras≤PopulationSources20258.source083.plan.scale*195336819379 := by decide +kernel
private theorem from19866To2564 : Segment 55 19866 20068 2505 2564 :=
  paid (pc:=75) (v:=195336819379) (by decide) PopulationSources20258.source083_valid (by decide +kernel) fee68At20068 (by decide +kernel)

private theorem from19866To2566 : Segment 55 19866 20068 2564 2566 :=
  paid (pc:=75) (v:=195336819379) (by decide) PopulationSources20258.source083_valid (by decide +kernel) fee68At20068 (by decide +kernel)

private theorem fee69At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source086.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source086.extras≤PopulationSources20258.source086.plan.scale*232746353433 := by decide +kernel
private theorem from19866To2696 : Segment 55 19866 20068 2566 2696 :=
  paid (pc:=74) (v:=232746353433) (by decide) PopulationSources20258.source086_valid (by decide +kernel) fee69At20068 (by decide +kernel)

private theorem fee70At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source085.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source085.extras≤PopulationSources20258.source085.plan.scale*214914853075 := by decide +kernel
private theorem from19866To2890 : Segment 55 19866 20068 2696 2890 :=
  paid (pc:=72) (v:=214914853075) (by decide) PopulationSources20258.source085_valid (by decide +kernel) fee70At20068 (by decide +kernel)

private theorem fee65At20068 :
    PopulationFees20258.bill (n:=20068) (PopulationFees20258.tabulate (20068-1) 256) PopulationSources20258.source081.plan.table+
      4*20068*NaturalPopulation20258.weights PopulationSources20258.source081.extras≤PopulationSources20258.source081.plan.scale*260676225870 := by decide +kernel
private theorem from19866To2971 : Segment 55 19866 20068 2890 2971 :=
  paid (pc:=66) (v:=260676225870) (by decide) PopulationSources20258.source081_valid (by decide +kernel) fee65At20068 (by decide +kernel)

private theorem range19866 : Win 55 19866 20068 :=
  complete (by decide) (by decide) (join_population (join_population (join_population from19866To2382 from19866To2428) (join_population from19866To2505 from19866To2564)) (join_population (join_population from19866To2566 from19866To2696) (join_population from19866To2890 from19866To2971)))

private theorem fee66At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source082.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source082.extras≤PopulationSources20258.source082.plan.scale*124092115716 := by decide +kernel
private theorem from20069To2400 : Segment 55 20069 20257 0 2400 :=
  paid (pc:=77) (v:=124092115716) (by decide) PopulationSources20258.source082_valid (by decide +kernel) fee66At20257 (by decide +kernel)

private theorem fee61At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source075.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source075.extras≤PopulationSources20258.source075.plan.scale*167159144283 := by decide +kernel
private theorem from20069To2446 : Segment 55 20069 20257 2400 2446 :=
  paid (pc:=77) (v:=167159144283) (by decide) PopulationSources20258.source075_valid (by decide +kernel) fee61At20257 (by decide +kernel)

private theorem fee67At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source084.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source084.extras≤PopulationSources20258.source084.plan.scale*205716956035 := by decide +kernel
private theorem from20069To2523 : Segment 55 20069 20257 2446 2523 :=
  paid (pc:=76) (v:=205716956035) (by decide) PopulationSources20258.source084_valid (by decide +kernel) fee67At20257 (by decide +kernel)

private theorem fee68At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source083.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source083.extras≤PopulationSources20258.source083.plan.scale*198701486653 := by decide +kernel
private theorem from20069To2579 : Segment 55 20069 20257 2523 2579 :=
  paid (pc:=75) (v:=198701486653) (by decide) PopulationSources20258.source083_valid (by decide +kernel) fee68At20257 (by decide +kernel)

private theorem fee69At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source086.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source086.extras≤PopulationSources20258.source086.plan.scale*236747299445 := by decide +kernel
private theorem from20069To2707 : Segment 55 20069 20257 2579 2707 :=
  paid (pc:=74) (v:=236747299445) (by decide) PopulationSources20258.source086_valid (by decide +kernel) fee69At20257 (by decide +kernel)

private theorem fee70At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source085.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source085.extras≤PopulationSources20258.source085.plan.scale*218620520045 := by decide +kernel
private theorem from20069To2896 : Segment 55 20069 20257 2707 2896 :=
  paid (pc:=72) (v:=218620520045) (by decide) PopulationSources20258.source085_valid (by decide +kernel) fee70At20257 (by decide +kernel)

private theorem fee65At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source081.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source081.extras≤PopulationSources20258.source081.plan.scale*265212928796 := by decide +kernel
private theorem from20069To2971 : Segment 55 20069 20257 2896 2971 :=
  paid (pc:=67) (v:=265212928796) (by decide) PopulationSources20258.source081_valid (by decide +kernel) fee65At20257 (by decide +kernel)

private theorem range20069 : Win 55 20069 20257 :=
  complete (by decide) (by decide) (join_population (join_population from20069To2400 (join_population from20069To2446 from20069To2523)) (join_population (join_population from20069To2579 from20069To2707) (join_population from20069To2896 from20069To2971)))

theorem bridge55 : Win 55 19683 20257 :=
  (join_ground range19683 (join_ground range19866 range20069))

end JSP233.Credit19227
