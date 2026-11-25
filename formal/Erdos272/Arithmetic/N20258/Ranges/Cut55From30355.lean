module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source066
public import Erdos272.Arithmetic.N20258.Sources.Source080
public import Erdos272.Arithmetic.N20258.Sources.Source082
public import Erdos272.Arithmetic.N20258.Sources.Source087

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests55_082_0 : ∀ z∈source082.plan.table,z.1.Valid 55 0 := by decide +kernel
private theorem fee55_082_32254 :
    PopulationFees20258.bill (n:=32254) (PopulationFees20258.tabulate (32254-1) 256) source082.plan.table+
      4*32254*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*295854473054 := by decide +kernel
private theorem range55From30355To2782 : Segment 55 30355 32254 0 2782 :=
  paid (pc:=76) (v:=295854473054) (by decide) source082_valid tests55_082_0 fee55_082_32254 (by decide +kernel)

private theorem tests55_066_2782 : ∀ z∈source066.plan.table,z.1.Valid 55 2782 := by decide +kernel
private theorem fee55_066_32254 :
    PopulationFees20258.bill (n:=32254) (PopulationFees20258.tabulate (32254-1) 256) source066.plan.table+
      4*32254*NaturalPopulation20258.weights source066.extras≤source066.plan.scale*422393232110 := by decide +kernel
private theorem range55From30355To2883 : Segment 55 30355 32254 2782 2883 :=
  paid (pc:=76) (v:=422393232110) (by decide) source066_valid tests55_066_2782 fee55_066_32254 (by decide +kernel)

private theorem tests55_080_2883 : ∀ z∈source080.plan.table,z.1.Valid 55 2883 := by decide +kernel
private theorem fee55_080_32254 :
    PopulationFees20258.bill (n:=32254) (PopulationFees20258.tabulate (32254-1) 256) source080.plan.table+
      4*32254*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*475031952677 := by decide +kernel
private theorem range55From30355To2969 : Segment 55 30355 32254 2883 2969 :=
  paid (pc:=75) (v:=475031952677) (by decide) source080_valid tests55_080_2883 fee55_080_32254 (by decide +kernel)

private theorem tests55_080_2969 : ∀ z∈source080.plan.table,z.1.Valid 55 2969 := by decide +kernel
private theorem range55From30355To2971 : Segment 55 30355 32254 2969 2971 :=
  paid (pc:=75) (v:=475031952677) (by decide) source080_valid tests55_080_2969 fee55_080_32254 (by decide +kernel)

private theorem range55From30355 : Win 55 30355 32254 :=
  complete (by decide) (by decide) (join_population (join_population range55From30355To2782 range55From30355To2883) (join_population range55From30355To2969 range55From30355To2971))

private theorem fee55_082_34708 :
    PopulationFees20258.bill (n:=34708) (PopulationFees20258.tabulate (34708-1) 256) source082.plan.table+
      4*34708*NaturalPopulation20258.weights source082.extras≤source082.plan.scale*339911832578 := by decide +kernel
private theorem range55From32255To2820 : Segment 55 32255 34708 0 2820 :=
  paid (pc:=75) (v:=339911832578) (by decide) source082_valid tests55_082_0 fee55_082_34708 (by decide +kernel)

private theorem tests55_087_2820 : ∀ z∈source087.plan.table,z.1.Valid 55 2820 := by decide +kernel
private theorem fee55_087_34708 :
    PopulationFees20258.bill (n:=34708) (PopulationFees20258.tabulate (34708-1) 256) source087.plan.table+
      4*34708*NaturalPopulation20258.weights source087.extras≤source087.plan.scale*549798172401 := by decide +kernel
private theorem range55From32255To2960 : Segment 55 32255 34708 2820 2960 :=
  paid (pc:=75) (v:=549798172401) (by decide) source087_valid tests55_087_2820 fee55_087_34708 (by decide +kernel)

private theorem tests55_080_2960 : ∀ z∈source080.plan.table,z.1.Valid 55 2960 := by decide +kernel
private theorem fee55_080_34708 :
    PopulationFees20258.bill (n:=34708) (PopulationFees20258.tabulate (34708-1) 256) source080.plan.table+
      4*34708*NaturalPopulation20258.weights source080.extras≤source080.plan.scale*545243649881 := by decide +kernel
private theorem range55From32255To2971 : Segment 55 32255 34708 2960 2971 :=
  paid (pc:=75) (v:=545243649881) (by decide) source080_valid tests55_080_2960 fee55_080_34708 (by decide +kernel)

private theorem range55From32255 : Win 55 32255 34708 :=
  complete (by decide) (by decide) (join_population range55From32255To2820 (join_population range55From32255To2960 range55From32255To2971))

private theorem range55From34709 : Win 55 34709 39999 :=
  short (by decide) (by decide)

theorem cut55From30355 : Win 55 30355 39999 :=
  (join_ground range55From30355 (join_ground range55From32255 range55From34709))

end JSP233.FiniteCutRanges20258
