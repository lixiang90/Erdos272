module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source113

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests63_113_0 : ∀ z∈source113.plan.table,z.1.Valid 63 0 := by decide +kernel
private theorem fee63_113_28612 :
    PopulationFees20258.bill (n:=28612) (PopulationFees20258.tabulate (28612-1) 256) source113.plan.table+
      4*28612*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*357946278770 := by decide +kernel
private theorem range63From27881To3505 : Segment 63 27881 28612 0 3505 :=
  paid (pc:=74) (v:=357946278770) (by decide) source113_valid tests63_113_0 fee63_113_28612 (by decide +kernel)

private theorem tests63_113_3505 : ∀ z∈source113.plan.table,z.1.Valid 63 3505 := by decide +kernel
private theorem range63From27881To3529 : Segment 63 27881 28612 3505 3529 :=
  paid (pc:=74) (v:=357946278770) (by decide) source113_valid tests63_113_3505 fee63_113_28612 (by decide +kernel)

private theorem tests63_108_3529 : ∀ z∈source108.plan.table,z.1.Valid 63 3529 := by decide +kernel
private theorem fee63_108_28612 :
    PopulationFees20258.bill (n:=28612) (PopulationFees20258.tabulate (28612-1) 256) source108.plan.table+
      4*28612*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*379069085900 := by decide +kernel
private theorem range63From27881To3837 : Segment 63 27881 28612 3529 3837 :=
  paid (pc:=72) (v:=379069085900) (by decide) source108_valid tests63_108_3529 fee63_108_28612 (by decide +kernel)

private theorem tests63_112_3837 : ∀ z∈source112.plan.table,z.1.Valid 63 3837 := by decide +kernel
private theorem fee63_112_28612 :
    PopulationFees20258.bill (n:=28612) (PopulationFees20258.tabulate (28612-1) 256) source112.plan.table+
      4*28612*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*396395265992 := by decide +kernel
private theorem range63From27881To3907 : Segment 63 27881 28612 3837 3907 :=
  paid (pc:=70) (v:=396395265992) (by decide) source112_valid tests63_112_3837 fee63_112_28612 (by decide +kernel)

private theorem range63From27881 : Win 63 27881 28612 :=
  complete (by decide) (by decide) (join_population (join_population range63From27881To3505 range63From27881To3529) (join_population range63From27881To3837 range63From27881To3907))

private theorem fee63_113_29448 :
    PopulationFees20258.bill (n:=29448) (PopulationFees20258.tabulate (29448-1) 256) source113.plan.table+
      4*29448*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*377437892532 := by decide +kernel
private theorem range63From28613To3507 : Segment 63 28613 29448 0 3507 :=
  paid (pc:=74) (v:=377437892532) (by decide) source113_valid tests63_113_0 fee63_113_29448 (by decide +kernel)

private theorem tests63_113_3507 : ∀ z∈source113.plan.table,z.1.Valid 63 3507 := by decide +kernel
private theorem range63From28613To3529 : Segment 63 28613 29448 3507 3529 :=
  paid (pc:=74) (v:=377437892532) (by decide) source113_valid tests63_113_3507 fee63_113_29448 (by decide +kernel)

private theorem fee63_108_29448 :
    PopulationFees20258.bill (n:=29448) (PopulationFees20258.tabulate (29448-1) 256) source108.plan.table+
      4*29448*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*400044050049 := by decide +kernel
private theorem range63From28613To3811 : Segment 63 28613 29448 3529 3811 :=
  paid (pc:=72) (v:=400044050049) (by decide) source108_valid tests63_108_3529 fee63_108_29448 (by decide +kernel)

private theorem tests63_112_3811 : ∀ z∈source112.plan.table,z.1.Valid 63 3811 := by decide +kernel
private theorem fee63_112_29448 :
    PopulationFees20258.bill (n:=29448) (PopulationFees20258.tabulate (29448-1) 256) source112.plan.table+
      4*29448*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*418156602858 := by decide +kernel
private theorem range63From28613To3907 : Segment 63 28613 29448 3811 3907 :=
  paid (pc:=71) (v:=418156602858) (by decide) source112_valid tests63_112_3811 fee63_112_29448 (by decide +kernel)

private theorem range63From28613 : Win 63 28613 29448 :=
  complete (by decide) (by decide) (join_population (join_population range63From28613To3507 range63From28613To3529) (join_population range63From28613To3811 range63From28613To3907))

private theorem fee63_113_30420 :
    PopulationFees20258.bill (n:=30420) (PopulationFees20258.tabulate (30420-1) 256) source113.plan.table+
      4*30420*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*400762840519 := by decide +kernel
private theorem range63From29449To3509 : Segment 63 29449 30420 0 3509 :=
  paid (pc:=74) (v:=400762840519) (by decide) source113_valid tests63_113_0 fee63_113_30420 (by decide +kernel)

private theorem tests63_113_3509 : ∀ z∈source113.plan.table,z.1.Valid 63 3509 := by decide +kernel
private theorem range63From29449To3529 : Segment 63 29449 30420 3509 3529 :=
  paid (pc:=74) (v:=400762840519) (by decide) source113_valid tests63_113_3509 fee63_113_30420 (by decide +kernel)

private theorem fee63_108_30420 :
    PopulationFees20258.bill (n:=30420) (PopulationFees20258.tabulate (30420-1) 256) source108.plan.table+
      4*30420*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*424788992215 := by decide +kernel
private theorem range63From29449To3787 : Segment 63 29449 30420 3529 3787 :=
  paid (pc:=73) (v:=424788992215) (by decide) source108_valid tests63_108_3529 fee63_108_30420 (by decide +kernel)

private theorem tests63_112_3787 : ∀ z∈source112.plan.table,z.1.Valid 63 3787 := by decide +kernel
private theorem fee63_112_30420 :
    PopulationFees20258.bill (n:=30420) (PopulationFees20258.tabulate (30420-1) 256) source112.plan.table+
      4*30420*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*444158553474 := by decide +kernel
private theorem range63From29449To3907 : Segment 63 29449 30420 3787 3907 :=
  paid (pc:=71) (v:=444158553474) (by decide) source112_valid tests63_112_3787 fee63_112_30420 (by decide +kernel)

private theorem range63From29449 : Win 63 29449 30420 :=
  complete (by decide) (by decide) (join_population (join_population range63From29449To3509 range63From29449To3529) (join_population range63From29449To3787 range63From29449To3907))

private theorem fee63_113_31570 :
    PopulationFees20258.bill (n:=31570) (PopulationFees20258.tabulate (31570-1) 256) source113.plan.table+
      4*31570*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*429300291505 := by decide +kernel
private theorem range63From30421To3512 : Segment 63 30421 31570 0 3512 :=
  paid (pc:=75) (v:=429300291505) (by decide) source113_valid tests63_113_0 fee63_113_31570 (by decide +kernel)

private theorem tests63_113_3512 : ∀ z∈source113.plan.table,z.1.Valid 63 3512 := by decide +kernel
private theorem range63From30421To3529 : Segment 63 30421 31570 3512 3529 :=
  paid (pc:=74) (v:=429300291505) (by decide) source113_valid tests63_113_3512 fee63_113_31570 (by decide +kernel)

private theorem fee63_108_31570 :
    PopulationFees20258.bill (n:=31570) (PopulationFees20258.tabulate (31570-1) 256) source108.plan.table+
      4*31570*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*455294391806 := by decide +kernel
private theorem range63From30421To3763 : Segment 63 30421 31570 3529 3763 :=
  paid (pc:=73) (v:=455294391806) (by decide) source108_valid tests63_108_3529 fee63_108_31570 (by decide +kernel)

private theorem tests63_112_3763 : ∀ z∈source112.plan.table,z.1.Valid 63 3763 := by decide +kernel
private theorem fee63_112_31570 :
    PopulationFees20258.bill (n:=31570) (PopulationFees20258.tabulate (31570-1) 256) source112.plan.table+
      4*31570*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*476206659288 := by decide +kernel
private theorem range63From30421To3907 : Segment 63 30421 31570 3763 3907 :=
  paid (pc:=72) (v:=476206659288) (by decide) source112_valid tests63_112_3763 fee63_112_31570 (by decide +kernel)

private theorem range63From30421 : Win 63 30421 31570 :=
  complete (by decide) (by decide) (join_population (join_population range63From30421To3512 range63From30421To3529) (join_population range63From30421To3763 range63From30421To3907))

private theorem fee63_113_32957 :
    PopulationFees20258.bill (n:=32957) (PopulationFees20258.tabulate (32957-1) 256) source113.plan.table+
      4*32957*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*465178990468 := by decide +kernel
private theorem range63From31571To3514 : Segment 63 31571 32957 0 3514 :=
  paid (pc:=75) (v:=465178990468) (by decide) source113_valid tests63_113_0 fee63_113_32957 (by decide +kernel)

private theorem tests63_113_3514 : ∀ z∈source113.plan.table,z.1.Valid 63 3514 := by decide +kernel
private theorem range63From31571To3529 : Segment 63 31571 32957 3514 3529 :=
  paid (pc:=75) (v:=465178990468) (by decide) source113_valid tests63_113_3514 fee63_113_32957 (by decide +kernel)

private theorem fee63_108_32957 :
    PopulationFees20258.bill (n:=32957) (PopulationFees20258.tabulate (32957-1) 256) source108.plan.table+
      4*32957*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*493412851656 := by decide +kernel
private theorem range63From31571To3740 : Segment 63 31571 32957 3529 3740 :=
  paid (pc:=73) (v:=493412851656) (by decide) source108_valid tests63_108_3529 fee63_108_32957 (by decide +kernel)

private theorem tests63_112_3740 : ∀ z∈source112.plan.table,z.1.Valid 63 3740 := by decide +kernel
private theorem fee63_112_32957 :
    PopulationFees20258.bill (n:=32957) (PopulationFees20258.tabulate (32957-1) 256) source112.plan.table+
      4*32957*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*515829161260 := by decide +kernel
private theorem range63From31571To3907 : Segment 63 31571 32957 3740 3907 :=
  paid (pc:=72) (v:=515829161260) (by decide) source112_valid tests63_112_3740 fee63_112_32957 (by decide +kernel)

private theorem range63From31571 : Win 63 31571 32957 :=
  complete (by decide) (by decide) (join_population (join_population range63From31571To3514 range63From31571To3529) (join_population range63From31571To3740 range63From31571To3907))

private theorem fee63_113_34668 :
    PopulationFees20258.bill (n:=34668) (PopulationFees20258.tabulate (34668-1) 256) source113.plan.table+
      4*34668*NaturalPopulation20258.weights source113.extras≤source113.plan.scale*511080562195 := by decide +kernel
private theorem range63From32958To3517 : Segment 63 32958 34668 0 3517 :=
  paid (pc:=75) (v:=511080562195) (by decide) source113_valid tests63_113_0 fee63_113_34668 (by decide +kernel)

private theorem tests63_113_3517 : ∀ z∈source113.plan.table,z.1.Valid 63 3517 := by decide +kernel
private theorem range63From32958To3529 : Segment 63 32958 34668 3517 3529 :=
  paid (pc:=75) (v:=511080562195) (by decide) source113_valid tests63_113_3517 fee63_113_34668 (by decide +kernel)

private theorem fee63_108_34668 :
    PopulationFees20258.bill (n:=34668) (PopulationFees20258.tabulate (34668-1) 256) source108.plan.table+
      4*34668*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*542518568430 := by decide +kernel
private theorem range63From32958To3716 : Segment 63 32958 34668 3529 3716 :=
  paid (pc:=74) (v:=542518568430) (by decide) source108_valid tests63_108_3529 fee63_108_34668 (by decide +kernel)

private theorem tests63_112_3716 : ∀ z∈source112.plan.table,z.1.Valid 63 3716 := by decide +kernel
private theorem fee63_112_34668 :
    PopulationFees20258.bill (n:=34668) (PopulationFees20258.tabulate (34668-1) 256) source112.plan.table+
      4*34668*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*566999558350 := by decide +kernel
private theorem range63From32958To3907 : Segment 63 32958 34668 3716 3907 :=
  paid (pc:=72) (v:=566999558350) (by decide) source112_valid tests63_112_3716 fee63_112_34668 (by decide +kernel)

private theorem range63From32958 : Win 63 32958 34668 :=
  complete (by decide) (by decide) (join_population (join_population range63From32958To3517 range63From32958To3529) (join_population range63From32958To3716 range63From32958To3907))

theorem cut63From27881 : Win 63 27881 34668 :=
  (join_ground (join_ground range63From27881 (join_ground range63From28613 range63From29449)) (join_ground range63From30421 (join_ground range63From31571 range63From32958)))

end JSP233.FiniteCutRanges20258
