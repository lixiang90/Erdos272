module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source085
public import Erdos272.Arithmetic.N20258.Sources.Source087
public import Erdos272.Arithmetic.N20258.Sources.Source088
public import Erdos272.Arithmetic.N20258.Sources.Source089
public import Erdos272.Arithmetic.N20258.Sources.Source090
public import Erdos272.Arithmetic.N20258.Sources.Source092

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests56_088_0 : ∀ z∈source088.plan.table,z.1.Valid 56 0 := by decide +kernel
private theorem fee56_088_23133 :
    PopulationFees20258.bill (n:=23133) (PopulationFees20258.tabulate (23133-1) 256) source088.plan.table+
      4*23133*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*196141808390 := by decide +kernel
private theorem range56From22699To2604 : Segment 56 22699 23133 0 2604 :=
  paid (pc:=77) (v:=196141808390) (by decide) source088_valid tests56_088_0 fee56_088_23133 (by decide +kernel)

private theorem tests56_089_2604 : ∀ z∈source089.plan.table,z.1.Valid 56 2604 := by decide +kernel
private theorem fee56_089_23133 :
    PopulationFees20258.bill (n:=23133) (PopulationFees20258.tabulate (23133-1) 256) source089.plan.table+
      4*23133*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*289627000046 := by decide +kernel
private theorem range56From22699To2760 : Segment 56 22699 23133 2604 2760 :=
  paid (pc:=76) (v:=289627000046) (by decide) source089_valid tests56_089_2604 fee56_089_23133 (by decide +kernel)

private theorem tests56_085_2760 : ∀ z∈source085.plan.table,z.1.Valid 56 2760 := by decide +kernel
private theorem fee56_085_23133 :
    PopulationFees20258.bill (n:=23133) (PopulationFees20258.tabulate (23133-1) 256) source085.plan.table+
      4*23133*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*278263621483 := by decide +kernel
private theorem range56From22699To2831 : Segment 56 22699 23133 2760 2831 :=
  paid (pc:=75) (v:=278263621483) (by decide) source085_valid tests56_085_2760 fee56_085_23133 (by decide +kernel)

private theorem tests56_092_2831 : ∀ z∈source092.plan.table,z.1.Valid 56 2831 := by decide +kernel
private theorem fee56_092_23133 :
    PopulationFees20258.bill (n:=23133) (PopulationFees20258.tabulate (23133-1) 256) source092.plan.table+
      4*23133*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*259255406586 := by decide +kernel
private theorem range56From22699To2946 : Segment 56 22699 23133 2831 2946 :=
  paid (pc:=74) (v:=259255406586) (by decide) source092_valid tests56_092_2831 fee56_092_23133 (by decide +kernel)

private theorem tests56_090_2946 : ∀ z∈source090.plan.table,z.1.Valid 56 2946 := by decide +kernel
private theorem fee56_090_23133 :
    PopulationFees20258.bill (n:=23133) (PopulationFees20258.tabulate (23133-1) 256) source090.plan.table+
      4*23133*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*238449296199 := by decide +kernel
private theorem range56From22699To3077 : Segment 56 22699 23133 2946 3077 :=
  paid (pc:=73) (v:=238449296199) (by decide) source090_valid tests56_090_2946 fee56_090_23133 (by decide +kernel)

private theorem tests56_090_3077 : ∀ z∈source090.plan.table,z.1.Valid 56 3077 := by decide +kernel
private theorem range56From22699To3081 : Segment 56 22699 23133 3077 3081 :=
  paid (pc:=73) (v:=238449296199) (by decide) source090_valid tests56_090_3077 fee56_090_23133 (by decide +kernel)

private theorem range56From22699 : Win 56 22699 23133 :=
  complete (by decide) (by decide) (join_population (join_population range56From22699To2604 (join_population range56From22699To2760 range56From22699To2831)) (join_population range56From22699To2946 (join_population range56From22699To3077 range56From22699To3081)))

private theorem fee56_088_23598 :
    PopulationFees20258.bill (n:=23598) (PopulationFees20258.tabulate (23598-1) 256) source088.plan.table+
      4*23598*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*203349935052 := by decide +kernel
private theorem range56From23134To2627 : Segment 56 23134 23598 0 2627 :=
  paid (pc:=77) (v:=203349935052) (by decide) source088_valid tests56_088_0 fee56_088_23598 (by decide +kernel)

private theorem tests56_089_2627 : ∀ z∈source089.plan.table,z.1.Valid 56 2627 := by decide +kernel
private theorem fee56_089_23598 :
    PopulationFees20258.bill (n:=23598) (PopulationFees20258.tabulate (23598-1) 256) source089.plan.table+
      4*23598*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*300183784529 := by decide +kernel
private theorem range56From23134To2773 : Segment 56 23134 23598 2627 2773 :=
  paid (pc:=76) (v:=300183784529) (by decide) source089_valid tests56_089_2627 fee56_089_23598 (by decide +kernel)

private theorem tests56_085_2773 : ∀ z∈source085.plan.table,z.1.Valid 56 2773 := by decide +kernel
private theorem fee56_085_23598 :
    PopulationFees20258.bill (n:=23598) (PopulationFees20258.tabulate (23598-1) 256) source085.plan.table+
      4*23598*NaturalPopulation20258.weights source085.extras≤source085.plan.scale*288575263501 := by decide +kernel
private theorem range56From23134To2841 : Segment 56 23134 23598 2773 2841 :=
  paid (pc:=75) (v:=288575263501) (by decide) source085_valid tests56_085_2773 fee56_085_23598 (by decide +kernel)

private theorem tests56_087_2841 : ∀ z∈source087.plan.table,z.1.Valid 56 2841 := by decide +kernel
private theorem fee56_087_23598 :
    PopulationFees20258.bill (n:=23598) (PopulationFees20258.tabulate (23598-1) 256) source087.plan.table+
      4*23598*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*267985239428 := by decide +kernel
private theorem range56From23134To2956 : Segment 56 23134 23598 2841 2956 :=
  paid (pc:=74) (v:=267985239428) (by decide) source087_valid tests56_087_2841 fee56_087_23598 (by decide +kernel)

private theorem tests56_090_2956 : ∀ z∈source090.plan.table,z.1.Valid 56 2956 := by decide +kernel
private theorem fee56_090_23598 :
    PopulationFees20258.bill (n:=23598) (PopulationFees20258.tabulate (23598-1) 256) source090.plan.table+
      4*23598*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*247185579025 := by decide +kernel
private theorem range56From23134To3078 : Segment 56 23134 23598 2956 3078 :=
  paid (pc:=73) (v:=247185579025) (by decide) source090_valid tests56_090_2956 fee56_090_23598 (by decide +kernel)

private theorem tests56_090_3078 : ∀ z∈source090.plan.table,z.1.Valid 56 3078 := by decide +kernel
private theorem range56From23134To3081 : Segment 56 23134 23598 3078 3081 :=
  paid (pc:=73) (v:=247185579025) (by decide) source090_valid tests56_090_3078 fee56_090_23598 (by decide +kernel)

private theorem range56From23134 : Win 56 23134 23598 :=
  complete (by decide) (by decide) (join_population (join_population range56From23134To2627 (join_population range56From23134To2773 range56From23134To2841)) (join_population range56From23134To2956 (join_population range56From23134To3078 range56From23134To3081)))

private theorem fee56_088_24102 :
    PopulationFees20258.bill (n:=24102) (PopulationFees20258.tabulate (24102-1) 256) source088.plan.table+
      4*24102*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*211515303006 := by decide +kernel
private theorem range56From23599To2650 : Segment 56 23599 24102 0 2650 :=
  paid (pc:=77) (v:=211515303006) (by decide) source088_valid tests56_088_0 fee56_088_24102 (by decide +kernel)

private theorem tests56_089_2650 : ∀ z∈source089.plan.table,z.1.Valid 56 2650 := by decide +kernel
private theorem fee56_089_24102 :
    PopulationFees20258.bill (n:=24102) (PopulationFees20258.tabulate (24102-1) 256) source089.plan.table+
      4*24102*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*312087256541 := by decide +kernel
private theorem range56From23599To2786 : Segment 56 23599 24102 2650 2786 :=
  paid (pc:=76) (v:=312087256541) (by decide) source089_valid tests56_089_2650 fee56_089_24102 (by decide +kernel)

private theorem tests56_092_2786 : ∀ z∈source092.plan.table,z.1.Valid 56 2786 := by decide +kernel
private theorem fee56_092_24102 :
    PopulationFees20258.bill (n:=24102) (PopulationFees20258.tabulate (24102-1) 256) source092.plan.table+
      4*24102*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*279450349825 := by decide +kernel
private theorem range56From23599To2955 : Segment 56 23599 24102 2786 2955 :=
  paid (pc:=75) (v:=279450349825) (by decide) source092_valid tests56_092_2786 fee56_092_24102 (by decide +kernel)

private theorem tests56_090_2955 : ∀ z∈source090.plan.table,z.1.Valid 56 2955 := by decide +kernel
private theorem fee56_090_24102 :
    PopulationFees20258.bill (n:=24102) (PopulationFees20258.tabulate (24102-1) 256) source090.plan.table+
      4*24102*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*257118466471 := by decide +kernel
private theorem range56From23599To3078 : Segment 56 23599 24102 2955 3078 :=
  paid (pc:=74) (v:=257118466471) (by decide) source090_valid tests56_090_2955 fee56_090_24102 (by decide +kernel)

private theorem range56From23599To3081 : Segment 56 23599 24102 3078 3081 :=
  paid (pc:=74) (v:=257118466471) (by decide) source090_valid tests56_090_3078 fee56_090_24102 (by decide +kernel)

private theorem range56From23599 : Win 56 23599 24102 :=
  complete (by decide) (by decide) (join_population (join_population range56From23599To2650 range56From23599To2786) (join_population range56From23599To2955 (join_population range56From23599To3078 range56From23599To3081)))

private theorem fee56_088_24656 :
    PopulationFees20258.bill (n:=24656) (PopulationFees20258.tabulate (24656-1) 256) source088.plan.table+
      4*24656*NaturalPopulation20258.weights source088.extras≤source088.plan.scale*220637356884 := by decide +kernel
private theorem range56From24103To2673 : Segment 56 24103 24656 0 2673 :=
  paid (pc:=77) (v:=220637356884) (by decide) source088_valid tests56_088_0 fee56_088_24656 (by decide +kernel)

private theorem tests56_089_2673 : ∀ z∈source089.plan.table,z.1.Valid 56 2673 := by decide +kernel
private theorem fee56_089_24656 :
    PopulationFees20258.bill (n:=24656) (PopulationFees20258.tabulate (24656-1) 256) source089.plan.table+
      4*24656*NaturalPopulation20258.weights source089.extras≤source089.plan.scale*325402454812 := by decide +kernel
private theorem range56From24103To2798 : Segment 56 24103 24656 2673 2798 :=
  paid (pc:=76) (v:=325402454812) (by decide) source089_valid tests56_089_2673 fee56_089_24656 (by decide +kernel)

private theorem tests56_092_2798 : ∀ z∈source092.plan.table,z.1.Valid 56 2798 := by decide +kernel
private theorem fee56_092_24656 :
    PopulationFees20258.bill (n:=24656) (PopulationFees20258.tabulate (24656-1) 256) source092.plan.table+
      4*24656*NaturalPopulation20258.weights source092.extras≤source092.plan.scale*291430707099 := by decide +kernel
private theorem range56From24103To2961 : Segment 56 24103 24656 2798 2961 :=
  paid (pc:=75) (v:=291430707099) (by decide) source092_valid tests56_092_2798 fee56_092_24656 (by decide +kernel)

private theorem tests56_090_2961 : ∀ z∈source090.plan.table,z.1.Valid 56 2961 := by decide +kernel
private theorem fee56_090_24656 :
    PopulationFees20258.bill (n:=24656) (PopulationFees20258.tabulate (24656-1) 256) source090.plan.table+
      4*24656*NaturalPopulation20258.weights source090.extras≤source090.plan.scale*268195784204 := by decide +kernel
private theorem range56From24103To3078 : Segment 56 24103 24656 2961 3078 :=
  paid (pc:=74) (v:=268195784204) (by decide) source090_valid tests56_090_2961 fee56_090_24656 (by decide +kernel)

private theorem range56From24103To3081 : Segment 56 24103 24656 3078 3081 :=
  paid (pc:=74) (v:=268195784204) (by decide) source090_valid tests56_090_3078 fee56_090_24656 (by decide +kernel)

private theorem range56From24103 : Win 56 24103 24656 :=
  complete (by decide) (by decide) (join_population (join_population range56From24103To2673 range56From24103To2798) (join_population range56From24103To2961 (join_population range56From24103To3078 range56From24103To3081)))

theorem cut56From22699 : Win 56 22699 24656 :=
  (join_ground (join_ground range56From22699 range56From23134) (join_ground range56From23599 range56From24103))

end JSP233.FiniteCutRanges20258
