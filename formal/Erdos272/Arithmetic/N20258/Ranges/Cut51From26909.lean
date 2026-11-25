module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source035
public import Erdos272.Arithmetic.N20258.Sources.Source036
public import Erdos272.Arithmetic.N20258.Sources.Source043
public import Erdos272.Arithmetic.N20258.Sources.Source045
public import Erdos272.Arithmetic.N20258.Sources.Source046

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests51_036_0 : ∀ z∈source036.plan.table,z.1.Valid 51 0 := by decide +kernel
private theorem fee51_036_28572 :
    PopulationFees20258.bill (n:=28572) (PopulationFees20258.tabulate (28572-1) 256) source036.plan.table+
      4*28572*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*226229721242 := by decide +kernel
private theorem range51From26909To2396 : Segment 51 26909 28572 0 2396 :=
  paid (pc:=77) (v:=226229721242) (by decide) source036_valid tests51_036_0 fee51_036_28572 (by decide +kernel)

private theorem tests51_043_2396 : ∀ z∈source043.plan.table,z.1.Valid 51 2396 := by decide +kernel
private theorem fee51_043_28572 :
    PopulationFees20258.bill (n:=28572) (PopulationFees20258.tabulate (28572-1) 256) source043.plan.table+
      4*28572*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*321463466012 := by decide +kernel
private theorem range51From26909To2495 : Segment 51 26909 28572 2396 2495 :=
  paid (pc:=76) (v:=321463466012) (by decide) source043_valid tests51_043_2396 fee51_043_28572 (by decide +kernel)

private theorem tests51_045_2495 : ∀ z∈source045.plan.table,z.1.Valid 51 2495 := by decide +kernel
private theorem fee51_045_28572 :
    PopulationFees20258.bill (n:=28572) (PopulationFees20258.tabulate (28572-1) 256) source045.plan.table+
      4*28572*NaturalPopulation20258.weights source045.extras≤source045.plan.scale*389758507650 := by decide +kernel
private theorem range51From26909To2501 : Segment 51 26909 28572 2495 2501 :=
  paid (pc:=76) (v:=389758507650) (by decide) source045_valid tests51_045_2495 fee51_045_28572 (by decide +kernel)

private theorem tests51_045_2501 : ∀ z∈source045.plan.table,z.1.Valid 51 2501 := by decide +kernel
private theorem range51From26909To2503 : Segment 51 26909 28572 2501 2503 :=
  paid (pc:=76) (v:=389758507650) (by decide) source045_valid tests51_045_2501 fee51_045_28572 (by decide +kernel)

private theorem tests51_046_2503 : ∀ z∈source046.plan.table,z.1.Valid 51 2503 := by decide +kernel
private theorem fee51_046_28572 :
    PopulationFees20258.bill (n:=28572) (PopulationFees20258.tabulate (28572-1) 256) source046.plan.table+
      4*28572*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*368176846324 := by decide +kernel
private theorem range51From26909To2551 : Segment 51 26909 28572 2503 2551 :=
  paid (pc:=76) (v:=368176846324) (by decide) source046_valid tests51_046_2503 fee51_046_28572 (by decide +kernel)

private theorem range51From26909 : Win 51 26909 28572 :=
  complete (by decide) (by decide) (join_population (join_population range51From26909To2396 range51From26909To2495) (join_population range51From26909To2501 (join_population range51From26909To2503 range51From26909To2551)))

private theorem fee51_036_30764 :
    PopulationFees20258.bill (n:=30764) (PopulationFees20258.tabulate (30764-1) 256) source036.plan.table+
      4*30764*NaturalPopulation20258.weights source036.extras≤source036.plan.scale*259955994043 := by decide +kernel
private theorem range51From28573To2423 : Segment 51 28573 30764 0 2423 :=
  paid (pc:=76) (v:=259955994043) (by decide) source036_valid tests51_036_0 fee51_036_30764 (by decide +kernel)

private theorem tests51_043_2423 : ∀ z∈source043.plan.table,z.1.Valid 51 2423 := by decide +kernel
private theorem fee51_043_30764 :
    PopulationFees20258.bill (n:=30764) (PopulationFees20258.tabulate (30764-1) 256) source043.plan.table+
      4*30764*NaturalPopulation20258.weights source043.extras≤source043.plan.scale*369202724163 := by decide +kernel
private theorem range51From28573To2502 : Segment 51 28573 30764 2423 2502 :=
  paid (pc:=75) (v:=369202724163) (by decide) source043_valid tests51_043_2423 fee51_043_30764 (by decide +kernel)

private theorem tests51_035_2502 : ∀ z∈source035.plan.table,z.1.Valid 51 2502 := by decide +kernel
private theorem fee51_035_30764 :
    PopulationFees20258.bill (n:=30764) (PopulationFees20258.tabulate (30764-1) 256) source035.plan.table+
      4*30764*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*368677672886 := by decide +kernel
private theorem range51From28573To2503 : Segment 51 28573 30764 2502 2503 :=
  paid (pc:=75) (v:=368677672886) (by decide) source035_valid tests51_035_2502 fee51_035_30764 (by decide +kernel)

private theorem fee51_046_30764 :
    PopulationFees20258.bill (n:=30764) (PopulationFees20258.tabulate (30764-1) 256) source046.plan.table+
      4*30764*NaturalPopulation20258.weights source046.extras≤source046.plan.scale*422761516179 := by decide +kernel
private theorem range51From28573To2551 : Segment 51 28573 30764 2503 2551 :=
  paid (pc:=75) (v:=422761516179) (by decide) source046_valid tests51_046_2503 fee51_046_30764 (by decide +kernel)

private theorem range51From28573 : Win 51 28573 30764 :=
  complete (by decide) (by decide) (join_population (join_population range51From28573To2423 range51From28573To2502) (join_population range51From28573To2503 range51From28573To2551))

private theorem range51From30765 : Win 51 30765 39999 :=
  short (by decide) (by decide)

theorem cut51From26909 : Win 51 26909 39999 :=
  (join_ground range51From26909 (join_ground range51From28573 range51From30765))

end JSP233.FiniteCutRanges20258
