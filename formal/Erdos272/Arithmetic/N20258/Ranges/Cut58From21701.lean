module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source100

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests58_098_0 : ∀ z∈source098.plan.table,z.1.Valid 58 0 := by decide +kernel
private theorem fee58_098_22110 :
    PopulationFees20258.bill (n:=22110) (PopulationFees20258.tabulate (22110-1) 256) source098.plan.table+
      4*22110*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*203128648852 := by decide +kernel
private theorem range58From21701To2724 : Segment 58 21701 22110 0 2724 :=
  paid (pc:=75) (v:=203128648852) (by decide) source098_valid tests58_098_0 fee58_098_22110 (by decide +kernel)

private theorem tests58_094_2724 : ∀ z∈source094.plan.table,z.1.Valid 58 2724 := by decide +kernel
private theorem fee58_094_22110 :
    PopulationFees20258.bill (n:=22110) (PopulationFees20258.tabulate (22110-1) 256) source094.plan.table+
      4*22110*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*253334315775 := by decide +kernel
private theorem range58From21701To2809 : Segment 58 21701 22110 2724 2809 :=
  paid (pc:=74) (v:=253334315775) (by decide) source094_valid tests58_094_2724 fee58_094_22110 (by decide +kernel)

private theorem tests58_094_2809 : ∀ z∈source094.plan.table,z.1.Valid 58 2809 := by decide +kernel
private theorem range58From21701To2813 : Segment 58 21701 22110 2809 2813 :=
  paid (pc:=74) (v:=253334315775) (by decide) source094_valid tests58_094_2809 fee58_094_22110 (by decide +kernel)

private theorem tests58_100_2813 : ∀ z∈source100.plan.table,z.1.Valid 58 2813 := by decide +kernel
private theorem fee58_100_22110 :
    PopulationFees20258.bill (n:=22110) (PopulationFees20258.tabulate (22110-1) 256) source100.plan.table+
      4*22110*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*281712726392 := by decide +kernel
private theorem range58From21701To3100 : Segment 58 21701 22110 2813 3100 :=
  paid (pc:=72) (v:=281712726392) (by decide) source100_valid tests58_100_2813 fee58_100_22110 (by decide +kernel)

private theorem tests58_096_3100 : ∀ z∈source096.plan.table,z.1.Valid 58 3100 := by decide +kernel
private theorem fee58_096_22110 :
    PopulationFees20258.bill (n:=22110) (PopulationFees20258.tabulate (22110-1) 256) source096.plan.table+
      4*22110*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*246600031110 := by decide +kernel
private theorem range58From21701To3307 : Segment 58 21701 22110 3100 3307 :=
  paid (pc:=69) (v:=246600031110) (by decide) source096_valid tests58_096_3100 fee58_096_22110 (by decide +kernel)

private theorem range58From21701 : Win 58 21701 22110 :=
  complete (by decide) (by decide) (join_population (join_population range58From21701To2724 range58From21701To2809) (join_population range58From21701To2813 (join_population range58From21701To3100 range58From21701To3307)))

private theorem fee58_098_22554 :
    PopulationFees20258.bill (n:=22554) (PopulationFees20258.tabulate (22554-1) 256) source098.plan.table+
      4*22554*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*210660799610 := by decide +kernel
private theorem range58From22111To2734 : Segment 58 22111 22554 0 2734 :=
  paid (pc:=75) (v:=210660799610) (by decide) source098_valid tests58_098_0 fee58_098_22554 (by decide +kernel)

private theorem tests58_094_2734 : ∀ z∈source094.plan.table,z.1.Valid 58 2734 := by decide +kernel
private theorem fee58_094_22554 :
    PopulationFees20258.bill (n:=22554) (PopulationFees20258.tabulate (22554-1) 256) source094.plan.table+
      4*22554*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*262699550177 := by decide +kernel
private theorem range58From22111To2809 : Segment 58 22111 22554 2734 2809 :=
  paid (pc:=74) (v:=262699550177) (by decide) source094_valid tests58_094_2734 fee58_094_22554 (by decide +kernel)

private theorem range58From22111To2812 : Segment 58 22111 22554 2809 2812 :=
  paid (pc:=74) (v:=262699550177) (by decide) source094_valid tests58_094_2809 fee58_094_22554 (by decide +kernel)

private theorem tests58_100_2812 : ∀ z∈source100.plan.table,z.1.Valid 58 2812 := by decide +kernel
private theorem fee58_100_22554 :
    PopulationFees20258.bill (n:=22554) (PopulationFees20258.tabulate (22554-1) 256) source100.plan.table+
      4*22554*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*292033610450 := by decide +kernel
private theorem range58From22111To3074 : Segment 58 22111 22554 2812 3074 :=
  paid (pc:=72) (v:=292033610450) (by decide) source100_valid tests58_100_2812 fee58_100_22554 (by decide +kernel)

private theorem tests58_097_3074 : ∀ z∈source097.plan.table,z.1.Valid 58 3074 := by decide +kernel
private theorem fee58_097_22554 :
    PopulationFees20258.bill (n:=22554) (PopulationFees20258.tabulate (22554-1) 256) source097.plan.table+
      4*22554*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*275293024593 := by decide +kernel
private theorem range58From22111To3227 : Segment 58 22111 22554 3074 3227 :=
  paid (pc:=71) (v:=275293024593) (by decide) source097_valid tests58_097_3074 fee58_097_22554 (by decide +kernel)

private theorem tests58_096_3227 : ∀ z∈source096.plan.table,z.1.Valid 58 3227 := by decide +kernel
private theorem fee58_096_22554 :
    PopulationFees20258.bill (n:=22554) (PopulationFees20258.tabulate (22554-1) 256) source096.plan.table+
      4*22554*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*255761532953 := by decide +kernel
private theorem range58From22111To3307 : Segment 58 22111 22554 3227 3307 :=
  paid (pc:=70) (v:=255761532953) (by decide) source096_valid tests58_096_3227 fee58_096_22554 (by decide +kernel)

private theorem range58From22111 : Win 58 22111 22554 :=
  complete (by decide) (by decide) (join_population (join_population range58From22111To2734 (join_population range58From22111To2809 range58From22111To2812)) (join_population range58From22111To3074 (join_population range58From22111To3227 range58From22111To3307)))

private theorem fee58_098_23042 :
    PopulationFees20258.bill (n:=23042) (PopulationFees20258.tabulate (23042-1) 256) source098.plan.table+
      4*23042*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*219039288049 := by decide +kernel
private theorem range58From22555To2741 : Segment 58 22555 23042 0 2741 :=
  paid (pc:=75) (v:=219039288049) (by decide) source098_valid tests58_098_0 fee58_098_23042 (by decide +kernel)

private theorem tests58_094_2741 : ∀ z∈source094.plan.table,z.1.Valid 58 2741 := by decide +kernel
private theorem fee58_094_23042 :
    PopulationFees20258.bill (n:=23042) (PopulationFees20258.tabulate (23042-1) 256) source094.plan.table+
      4*23042*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*273116287952 := by decide +kernel
private theorem range58From22555To2810 : Segment 58 22555 23042 2741 2810 :=
  paid (pc:=75) (v:=273116287952) (by decide) source094_valid tests58_094_2741 fee58_094_23042 (by decide +kernel)

private theorem tests58_094_2810 : ∀ z∈source094.plan.table,z.1.Valid 58 2810 := by decide +kernel
private theorem range58From22555To2812 : Segment 58 22555 23042 2810 2812 :=
  paid (pc:=75) (v:=273116287952) (by decide) source094_valid tests58_094_2810 fee58_094_23042 (by decide +kernel)

private theorem fee58_100_23042 :
    PopulationFees20258.bill (n:=23042) (PopulationFees20258.tabulate (23042-1) 256) source100.plan.table+
      4*23042*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*303566306804 := by decide +kernel
private theorem range58From22555To3051 : Segment 58 22555 23042 2812 3051 :=
  paid (pc:=73) (v:=303566306804) (by decide) source100_valid tests58_100_2812 fee58_100_23042 (by decide +kernel)

private theorem tests58_097_3051 : ∀ z∈source097.plan.table,z.1.Valid 58 3051 := by decide +kernel
private theorem fee58_097_23042 :
    PopulationFees20258.bill (n:=23042) (PopulationFees20258.tabulate (23042-1) 256) source097.plan.table+
      4*23042*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*286225599790 := by decide +kernel
private theorem range58From22555To3192 : Segment 58 22555 23042 3051 3192 :=
  paid (pc:=72) (v:=286225599790) (by decide) source097_valid tests58_097_3051 fee58_097_23042 (by decide +kernel)

private theorem tests58_096_3192 : ∀ z∈source096.plan.table,z.1.Valid 58 3192 := by decide +kernel
private theorem fee58_096_23042 :
    PopulationFees20258.bill (n:=23042) (PopulationFees20258.tabulate (23042-1) 256) source096.plan.table+
      4*23042*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*265975654889 := by decide +kernel
private theorem range58From22555To3307 : Segment 58 22555 23042 3192 3307 :=
  paid (pc:=71) (v:=265975654889) (by decide) source096_valid tests58_096_3192 fee58_096_23042 (by decide +kernel)

private theorem range58From22555 : Win 58 22555 23042 :=
  complete (by decide) (by decide) (join_population (join_population range58From22555To2741 (join_population range58From22555To2810 range58From22555To2812)) (join_population range58From22555To3051 (join_population range58From22555To3192 range58From22555To3307)))

private theorem fee58_098_23588 :
    PopulationFees20258.bill (n:=23588) (PopulationFees20258.tabulate (23588-1) 256) source098.plan.table+
      4*23588*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*228673660086 := by decide +kernel
private theorem range58From23043To2751 : Segment 58 23043 23588 0 2751 :=
  paid (pc:=75) (v:=228673660086) (by decide) source098_valid tests58_098_0 fee58_098_23588 (by decide +kernel)

private theorem tests58_094_2751 : ∀ z∈source094.plan.table,z.1.Valid 58 2751 := by decide +kernel
private theorem fee58_094_23588 :
    PopulationFees20258.bill (n:=23588) (PopulationFees20258.tabulate (23588-1) 256) source094.plan.table+
      4*23588*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*285027317361 := by decide +kernel
private theorem range58From23043To2810 : Segment 58 23043 23588 2751 2810 :=
  paid (pc:=75) (v:=285027317361) (by decide) source094_valid tests58_094_2751 fee58_094_23588 (by decide +kernel)

private theorem range58From23043To2812 : Segment 58 23043 23588 2810 2812 :=
  paid (pc:=75) (v:=285027317361) (by decide) source094_valid tests58_094_2810 fee58_094_23588 (by decide +kernel)

private theorem fee58_100_23588 :
    PopulationFees20258.bill (n:=23588) (PopulationFees20258.tabulate (23588-1) 256) source100.plan.table+
      4*23588*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*316774446573 := by decide +kernel
private theorem range58From23043To3029 : Segment 58 23043 23588 2812 3029 :=
  paid (pc:=73) (v:=316774446573) (by decide) source100_valid tests58_100_2812 fee58_100_23588 (by decide +kernel)

private theorem tests58_097_3029 : ∀ z∈source097.plan.table,z.1.Valid 58 3029 := by decide +kernel
private theorem fee58_097_23588 :
    PopulationFees20258.bill (n:=23588) (PopulationFees20258.tabulate (23588-1) 256) source097.plan.table+
      4*23588*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*298715118926 := by decide +kernel
private theorem range58From23043To3161 : Segment 58 23043 23588 3029 3161 :=
  paid (pc:=72) (v:=298715118926) (by decide) source097_valid tests58_097_3029 fee58_097_23588 (by decide +kernel)

private theorem tests58_096_3161 : ∀ z∈source096.plan.table,z.1.Valid 58 3161 := by decide +kernel
private theorem fee58_096_23588 :
    PopulationFees20258.bill (n:=23588) (PopulationFees20258.tabulate (23588-1) 256) source096.plan.table+
      4*23588*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*277625868946 := by decide +kernel
private theorem range58From23043To3307 : Segment 58 23043 23588 3161 3307 :=
  paid (pc:=71) (v:=277625868946) (by decide) source096_valid tests58_096_3161 fee58_096_23588 (by decide +kernel)

private theorem range58From23043 : Win 58 23043 23588 :=
  complete (by decide) (by decide) (join_population (join_population range58From23043To2751 (join_population range58From23043To2810 range58From23043To2812)) (join_population range58From23043To3029 (join_population range58From23043To3161 range58From23043To3307)))

theorem cut58From21701 : Win 58 21701 23588 :=
  (join_ground (join_ground range58From21701 range58From22111) (join_ground range58From22555 range58From23043))

end JSP233.FiniteCutRanges20258
