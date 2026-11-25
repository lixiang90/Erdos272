module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source047
public import Erdos272.Arithmetic.N20258.Sources.Source054
public import Erdos272.Arithmetic.N20258.Sources.Source057
public import Erdos272.Arithmetic.N20258.Sources.Source062
public import Erdos272.Arithmetic.N20258.Sources.Source068
public import Erdos272.Arithmetic.N20258.Sources.Source069
public import Erdos272.Arithmetic.N20258.Sources.Source070

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests53_057_0 : ∀ z∈source057.plan.table,z.1.Valid 53 0 := by decide +kernel
private theorem fee53_057_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source057.plan.table+
      4*28512*NaturalPopulation20258.weights source057.extras≤source057.plan.scale*271620447474 := by decide +kernel
private theorem range53From27073To2518 : Segment 53 27073 28512 0 2518 :=
  paid (pc:=77) (v:=271620447474) (by decide) source057_valid tests53_057_0 fee53_057_28512 (by decide +kernel)

private theorem tests53_068_2518 : ∀ z∈source068.plan.table,z.1.Valid 53 2518 := by decide +kernel
private theorem fee53_068_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source068.plan.table+
      4*28512*NaturalPopulation20258.weights source068.extras≤source068.plan.scale*374017829929 := by decide +kernel
private theorem range53From27073To2626 : Segment 53 27073 28512 2518 2626 :=
  paid (pc:=76) (v:=374017829929) (by decide) source068_valid tests53_068_2518 fee53_068_28512 (by decide +kernel)

private theorem tests53_070_2626 : ∀ z∈source070.plan.table,z.1.Valid 53 2626 := by decide +kernel
private theorem fee53_070_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source070.plan.table+
      4*28512*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*347615251249 := by decide +kernel
private theorem range53From27073To2702 : Segment 53 27073 28512 2626 2702 :=
  paid (pc:=76) (v:=347615251249) (by decide) source070_valid tests53_070_2626 fee53_070_28512 (by decide +kernel)

private theorem tests53_069_2702 : ∀ z∈source069.plan.table,z.1.Valid 53 2702 := by decide +kernel
private theorem fee53_069_28512 :
    PopulationFees20258.bill (n:=28512) (PopulationFees20258.tabulate (28512-1) 256) source069.plan.table+
      4*28512*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*328892518903 := by decide +kernel
private theorem range53From27073To2755 : Segment 53 27073 28512 2702 2755 :=
  paid (pc:=75) (v:=328892518903) (by decide) source069_valid tests53_069_2702 fee53_069_28512 (by decide +kernel)

private theorem tests53_069_2755 : ∀ z∈source069.plan.table,z.1.Valid 53 2755 := by decide +kernel
private theorem range53From27073To2757 : Segment 53 27073 28512 2755 2757 :=
  paid (pc:=75) (v:=328892518903) (by decide) source069_valid tests53_069_2755 fee53_069_28512 (by decide +kernel)

private theorem range53From27073 : Win 53 27073 28512 :=
  complete (by decide) (by decide) (join_population (join_population range53From27073To2518 range53From27073To2626) (join_population range53From27073To2702 (join_population range53From27073To2755 range53From27073To2757)))

private theorem tests53_047_0 : ∀ z∈source047.plan.table,z.1.Valid 53 0 := by decide +kernel
private theorem fee53_047_30348 :
    PopulationFees20258.bill (n:=30348) (PopulationFees20258.tabulate (30348-1) 256) source047.plan.table+
      4*30348*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*226953301099 := by decide +kernel
private theorem range53From28513To2552 : Segment 53 28513 30348 0 2552 :=
  paid (pc:=76) (v:=226953301099) (by decide) source047_valid tests53_047_0 fee53_047_30348 (by decide +kernel)

private theorem tests53_054_2552 : ∀ z∈source054.plan.table,z.1.Valid 53 2552 := by decide +kernel
private theorem fee53_054_30348 :
    PopulationFees20258.bill (n:=30348) (PopulationFees20258.tabulate (30348-1) 256) source054.plan.table+
      4*30348*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*418106055543 := by decide +kernel
private theorem range53From28513To2639 : Segment 53 28513 30348 2552 2639 :=
  paid (pc:=76) (v:=418106055543) (by decide) source054_valid tests53_054_2552 fee53_054_30348 (by decide +kernel)

private theorem tests53_070_2639 : ∀ z∈source070.plan.table,z.1.Valid 53 2639 := by decide +kernel
private theorem fee53_070_30348 :
    PopulationFees20258.bill (n:=30348) (PopulationFees20258.tabulate (30348-1) 256) source070.plan.table+
      4*30348*NaturalPopulation20258.weights source070.extras≤source070.plan.scale*390730394913 := by decide +kernel
private theorem range53From28513To2704 : Segment 53 28513 30348 2639 2704 :=
  paid (pc:=75) (v:=390730394913) (by decide) source070_valid tests53_070_2639 fee53_070_30348 (by decide +kernel)

private theorem tests53_069_2704 : ∀ z∈source069.plan.table,z.1.Valid 53 2704 := by decide +kernel
private theorem fee53_069_30348 :
    PopulationFees20258.bill (n:=30348) (PopulationFees20258.tabulate (30348-1) 256) source069.plan.table+
      4*30348*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*369799764702 := by decide +kernel
private theorem range53From28513To2756 : Segment 53 28513 30348 2704 2756 :=
  paid (pc:=75) (v:=369799764702) (by decide) source069_valid tests53_069_2704 fee53_069_30348 (by decide +kernel)

private theorem tests53_069_2756 : ∀ z∈source069.plan.table,z.1.Valid 53 2756 := by decide +kernel
private theorem range53From28513To2757 : Segment 53 28513 30348 2756 2757 :=
  paid (pc:=75) (v:=369799764702) (by decide) source069_valid tests53_069_2756 fee53_069_30348 (by decide +kernel)

private theorem range53From28513 : Win 53 28513 30348 :=
  complete (by decide) (by decide) (join_population (join_population range53From28513To2552 range53From28513To2639) (join_population range53From28513To2704 (join_population range53From28513To2756 range53From28513To2757)))

private theorem fee53_047_32742 :
    PopulationFees20258.bill (n:=32742) (PopulationFees20258.tabulate (32742-1) 256) source047.plan.table+
      4*32742*NaturalPopulation20258.weights source047.extras≤source047.plan.scale*261964617594 := by decide +kernel
private theorem range53From30349To2590 : Segment 53 30349 32742 0 2590 :=
  paid (pc:=76) (v:=261964617594) (by decide) source047_valid tests53_047_0 fee53_047_32742 (by decide +kernel)

private theorem tests53_054_2590 : ∀ z∈source054.plan.table,z.1.Valid 53 2590 := by decide +kernel
private theorem fee53_054_32742 :
    PopulationFees20258.bill (n:=32742) (PopulationFees20258.tabulate (32742-1) 256) source054.plan.table+
      4*32742*NaturalPopulation20258.weights source054.extras≤source054.plan.scale*482012417294 := by decide +kernel
private theorem range53From30349To2647 : Segment 53 30349 32742 2590 2647 :=
  paid (pc:=75) (v:=482012417294) (by decide) source054_valid tests53_054_2590 fee53_054_32742 (by decide +kernel)

private theorem tests53_062_2647 : ∀ z∈source062.plan.table,z.1.Valid 53 2647 := by decide +kernel
private theorem fee53_062_32742 :
    PopulationFees20258.bill (n:=32742) (PopulationFees20258.tabulate (32742-1) 256) source062.plan.table+
      4*32742*NaturalPopulation20258.weights source062.extras≤source062.plan.scale*447784573238 := by decide +kernel
private theorem range53From30349To2714 : Segment 53 30349 32742 2647 2714 :=
  paid (pc:=75) (v:=447784573238) (by decide) source062_valid tests53_062_2647 fee53_062_32742 (by decide +kernel)

private theorem tests53_069_2714 : ∀ z∈source069.plan.table,z.1.Valid 53 2714 := by decide +kernel
private theorem fee53_069_32742 :
    PopulationFees20258.bill (n:=32742) (PopulationFees20258.tabulate (32742-1) 256) source069.plan.table+
      4*32742*NaturalPopulation20258.weights source069.extras≤source069.plan.scale*426726612959 := by decide +kernel
private theorem range53From30349To2757 : Segment 53 30349 32742 2714 2757 :=
  paid (pc:=75) (v:=426726612959) (by decide) source069_valid tests53_069_2714 fee53_069_32742 (by decide +kernel)

private theorem range53From30349 : Win 53 30349 32742 :=
  complete (by decide) (by decide) (join_population (join_population range53From30349To2590 range53From30349To2647) (join_population range53From30349To2714 range53From30349To2757))

private theorem range53From32743 : Win 53 32743 39999 :=
  short (by decide) (by decide)

theorem cut53From27073 : Win 53 27073 39999 :=
  (join_ground (join_ground range53From27073 range53From28513) (join_ground range53From30349 range53From32743))

end JSP233.FiniteCutRanges20258
