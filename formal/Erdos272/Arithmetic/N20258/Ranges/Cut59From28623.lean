module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source101

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests59_101_0 : ∀ z∈source101.plan.table,z.1.Valid 59 0 := by decide +kernel
private theorem fee59_101_29424 :
    PopulationFees20258.bill (n:=29424) (PopulationFees20258.tabulate (29424-1) 256) source101.plan.table+
      4*29424*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*320989212610 := by decide +kernel
private theorem range59From28623To3146 : Segment 59 28623 29424 0 3146 :=
  paid (pc:=77) (v:=320989212610) (by decide) source101_valid tests59_101_0 fee59_101_29424 (by decide +kernel)

private theorem tests59_096_3146 : ∀ z∈source096.plan.table,z.1.Valid 59 3146 := by decide +kernel
private theorem fee59_096_29424 :
    PopulationFees20258.bill (n:=29424) (PopulationFees20258.tabulate (29424-1) 256) source096.plan.table+
      4*29424*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*417541822986 := by decide +kernel
private theorem range59From28623To3418 : Segment 59 28623 29424 3146 3418 :=
  paid (pc:=75) (v:=417541822986) (by decide) source096_valid tests59_096_3146 fee59_096_29424 (by decide +kernel)

private theorem tests59_096_3418 : ∀ z∈source096.plan.table,z.1.Valid 59 3418 := by decide +kernel
private theorem range59From28623To3423 : Segment 59 28623 29424 3418 3423 :=
  paid (pc:=75) (v:=417541822986) (by decide) source096_valid tests59_096_3418 fee59_096_29424 (by decide +kernel)

private theorem range59From28623 : Win 59 28623 29424 :=
  complete (by decide) (by decide) (join_population range59From28623To3146 (join_population range59From28623To3418 range59From28623To3423))

private theorem fee59_101_30364 :
    PopulationFees20258.bill (n:=30364) (PopulationFees20258.tabulate (30364-1) 256) source101.plan.table+
      4*30364*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*340352777059 := by decide +kernel
private theorem range59From29425To3168 : Segment 59 29425 30364 0 3168 :=
  paid (pc:=77) (v:=340352777059) (by decide) source101_valid tests59_101_0 fee59_101_30364 (by decide +kernel)

private theorem tests59_096_3168 : ∀ z∈source096.plan.table,z.1.Valid 59 3168 := by decide +kernel
private theorem fee59_096_30364 :
    PopulationFees20258.bill (n:=30364) (PopulationFees20258.tabulate (30364-1) 256) source096.plan.table+
      4*30364*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*443007323377 := by decide +kernel
private theorem range59From29425To3417 : Segment 59 29425 30364 3168 3417 :=
  paid (pc:=75) (v:=443007323377) (by decide) source096_valid tests59_096_3168 fee59_096_30364 (by decide +kernel)

private theorem tests59_096_3417 : ∀ z∈source096.plan.table,z.1.Valid 59 3417 := by decide +kernel
private theorem range59From29425To3423 : Segment 59 29425 30364 3417 3423 :=
  paid (pc:=75) (v:=443007323377) (by decide) source096_valid tests59_096_3417 fee59_096_30364 (by decide +kernel)

private theorem range59From29425 : Win 59 29425 30364 :=
  complete (by decide) (by decide) (join_population range59From29425To3168 (join_population range59From29425To3417 range59From29425To3423))

private theorem fee59_101_31488 :
    PopulationFees20258.bill (n:=31488) (PopulationFees20258.tabulate (31488-1) 256) source101.plan.table+
      4*31488*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*364313020778 := by decide +kernel
private theorem range59From30365To3191 : Segment 59 30365 31488 0 3191 :=
  paid (pc:=76) (v:=364313020778) (by decide) source101_valid tests59_101_0 fee59_101_31488 (by decide +kernel)

private theorem tests59_096_3191 : ∀ z∈source096.plan.table,z.1.Valid 59 3191 := by decide +kernel
private theorem fee59_096_31488 :
    PopulationFees20258.bill (n:=31488) (PopulationFees20258.tabulate (31488-1) 256) source096.plan.table+
      4*31488*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*473951718066 := by decide +kernel
private theorem range59From30365To3419 : Segment 59 30365 31488 3191 3419 :=
  paid (pc:=75) (v:=473951718066) (by decide) source096_valid tests59_096_3191 fee59_096_31488 (by decide +kernel)

private theorem tests59_096_3419 : ∀ z∈source096.plan.table,z.1.Valid 59 3419 := by decide +kernel
private theorem range59From30365To3423 : Segment 59 30365 31488 3419 3423 :=
  paid (pc:=75) (v:=473951718066) (by decide) source096_valid tests59_096_3419 fee59_096_31488 (by decide +kernel)

private theorem range59From30365 : Win 59 30365 31488 :=
  complete (by decide) (by decide) (join_population range59From30365To3191 (join_population range59From30365To3419 range59From30365To3423))

private theorem fee59_101_32852 :
    PopulationFees20258.bill (n:=32852) (PopulationFees20258.tabulate (32852-1) 256) source101.plan.table+
      4*32852*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*394392116113 := by decide +kernel
private theorem range59From31489To3215 : Segment 59 31489 32852 0 3215 :=
  paid (pc:=76) (v:=394392116113) (by decide) source101_valid tests59_101_0 fee59_101_32852 (by decide +kernel)

private theorem tests59_096_3215 : ∀ z∈source096.plan.table,z.1.Valid 59 3215 := by decide +kernel
private theorem fee59_096_32852 :
    PopulationFees20258.bill (n:=32852) (PopulationFees20258.tabulate (32852-1) 256) source096.plan.table+
      4*32852*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*513201720040 := by decide +kernel
private theorem range59From31489To3419 : Segment 59 31489 32852 3215 3419 :=
  paid (pc:=75) (v:=513201720040) (by decide) source096_valid tests59_096_3215 fee59_096_32852 (by decide +kernel)

private theorem range59From31489To3423 : Segment 59 31489 32852 3419 3423 :=
  paid (pc:=75) (v:=513201720040) (by decide) source096_valid tests59_096_3419 fee59_096_32852 (by decide +kernel)

private theorem range59From31489 : Win 59 31489 32852 :=
  complete (by decide) (by decide) (join_population range59From31489To3215 (join_population range59From31489To3419 range59From31489To3423))

private theorem fee59_101_34544 :
    PopulationFees20258.bill (n:=34544) (PopulationFees20258.tabulate (34544-1) 256) source101.plan.table+
      4*34544*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*433448508810 := by decide +kernel
private theorem range59From32853To3241 : Segment 59 32853 34544 0 3241 :=
  paid (pc:=76) (v:=433448508810) (by decide) source101_valid tests59_101_0 fee59_101_34544 (by decide +kernel)

private theorem tests59_096_3241 : ∀ z∈source096.plan.table,z.1.Valid 59 3241 := by decide +kernel
private theorem fee59_096_34544 :
    PopulationFees20258.bill (n:=34544) (PopulationFees20258.tabulate (34544-1) 256) source096.plan.table+
      4*34544*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*563812031268 := by decide +kernel
private theorem range59From32853To3419 : Segment 59 32853 34544 3241 3419 :=
  paid (pc:=75) (v:=563812031268) (by decide) source096_valid tests59_096_3241 fee59_096_34544 (by decide +kernel)

private theorem range59From32853To3423 : Segment 59 32853 34544 3419 3423 :=
  paid (pc:=75) (v:=563812031268) (by decide) source096_valid tests59_096_3419 fee59_096_34544 (by decide +kernel)

private theorem range59From32853 : Win 59 32853 34544 :=
  complete (by decide) (by decide) (join_population range59From32853To3241 (join_population range59From32853To3419 range59From32853To3423))

private theorem fee59_101_36684 :
    PopulationFees20258.bill (n:=36684) (PopulationFees20258.tabulate (36684-1) 256) source101.plan.table+
      4*36684*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*485349864628 := by decide +kernel
private theorem range59From34545To3269 : Segment 59 34545 36684 0 3269 :=
  paid (pc:=76) (v:=485349864628) (by decide) source101_valid tests59_101_0 fee59_101_36684 (by decide +kernel)

private theorem tests59_096_3269 : ∀ z∈source096.plan.table,z.1.Valid 59 3269 := by decide +kernel
private theorem fee59_096_36684 :
    PopulationFees20258.bill (n:=36684) (PopulationFees20258.tabulate (36684-1) 256) source096.plan.table+
      4*36684*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*631410252762 := by decide +kernel
private theorem range59From34545To3421 : Segment 59 34545 36684 3269 3421 :=
  paid (pc:=75) (v:=631410252762) (by decide) source096_valid tests59_096_3269 fee59_096_36684 (by decide +kernel)

private theorem tests59_096_3421 : ∀ z∈source096.plan.table,z.1.Valid 59 3421 := by decide +kernel
private theorem range59From34545To3423 : Segment 59 34545 36684 3421 3423 :=
  paid (pc:=75) (v:=631410252762) (by decide) source096_valid tests59_096_3421 fee59_096_36684 (by decide +kernel)

private theorem range59From34545 : Win 59 34545 36684 :=
  complete (by decide) (by decide) (join_population range59From34545To3269 (join_population range59From34545To3421 range59From34545To3423))

private theorem fee59_101_39454 :
    PopulationFees20258.bill (n:=39454) (PopulationFees20258.tabulate (39454-1) 256) source101.plan.table+
      4*39454*NaturalPopulation20258.weights source101.extras≤source101.plan.scale*557075090488 := by decide +kernel
private theorem range59From36685To3299 : Segment 59 36685 39454 0 3299 :=
  paid (pc:=75) (v:=557075090488) (by decide) source101_valid tests59_101_0 fee59_101_39454 (by decide +kernel)

private theorem tests59_096_3299 : ∀ z∈source096.plan.table,z.1.Valid 59 3299 := by decide +kernel
private theorem fee59_096_39454 :
    PopulationFees20258.bill (n:=39454) (PopulationFees20258.tabulate (39454-1) 256) source096.plan.table+
      4*39454*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*724457747309 := by decide +kernel
private theorem range59From36685To3420 : Segment 59 36685 39454 3299 3420 :=
  paid (pc:=74) (v:=724457747309) (by decide) source096_valid tests59_096_3299 fee59_096_39454 (by decide +kernel)

private theorem tests59_096_3420 : ∀ z∈source096.plan.table,z.1.Valid 59 3420 := by decide +kernel
private theorem range59From36685To3423 : Segment 59 36685 39454 3420 3423 :=
  paid (pc:=74) (v:=724457747309) (by decide) source096_valid tests59_096_3420 fee59_096_39454 (by decide +kernel)

private theorem range59From36685 : Win 59 36685 39454 :=
  complete (by decide) (by decide) (join_population range59From36685To3299 (join_population range59From36685To3420 range59From36685To3423))

private theorem range59From39455 : Win 59 39455 39999 :=
  short (by decide) (by decide)

theorem cut59From28623 : Win 59 28623 39999 :=
  (join_ground (join_ground (join_ground range59From28623 range59From29425) (join_ground range59From30365 range59From31489)) (join_ground (join_ground range59From32853 range59From34545) (join_ground range59From36685 range59From39455)))

end JSP233.FiniteCutRanges20258
