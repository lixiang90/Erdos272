module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source124
public import Erdos272.Arithmetic.N20258.Sources.Source125

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem range75From20258Price : ( .marked ⟨75,216,29,14000⟩ : ConcentratedBlocks20258.Source).Valid := by decide +kernel

private theorem range75From20258 : Win 75 20258 25264 :=
  classical_route (pc:=0) range75From20258Price (by decide +kernel)

private theorem tests75_125_0 : ∀ z∈source125.plan.table,z.1.Valid 75 0 := by decide +kernel
private theorem fee75_125_31132 :
    PopulationFees20258.bill (n:=31132) (PopulationFees20258.tabulate (31132-1) 256) source125.plan.table+
      4*31132*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*703894837711 := by decide +kernel
private theorem range75From25265To5551 : Segment 75 25265 31132 0 5551 :=
  paid (pc:=61) (v:=703894837711) (by decide) source125_valid tests75_125_0 fee75_125_31132 (by decide +kernel)

private theorem range75From25265 : Win 75 25265 31132 :=
  complete (by decide) (by decide) range75From25265To5551

private theorem fee75_125_35980 :
    PopulationFees20258.bill (n:=35980) (PopulationFees20258.tabulate (35980-1) 256) source125.plan.table+
      4*35980*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*912897832485 := by decide +kernel
private theorem range75From31133To4359 : Segment 75 31133 35980 0 4359 :=
  paid (pc:=58) (v:=912897832485) (by decide) source125_valid tests75_125_0 fee75_125_35980 (by decide +kernel)

private theorem tests75_125_4359 : ∀ z∈source125.plan.table,z.1.Valid 75 4359 := by decide +kernel
private theorem range75From31133To4543 : Segment 75 31133 35980 4359 4543 :=
  paid (pc:=57) (v:=912897832485) (by decide) source125_valid tests75_125_4359 fee75_125_35980 (by decide +kernel)

private theorem tests75_125_4543 : ∀ z∈source125.plan.table,z.1.Valid 75 4543 := by decide +kernel
private theorem range75From31133To4570 : Segment 75 31133 35980 4543 4570 :=
  paid (pc:=57) (v:=912897832485) (by decide) source125_valid tests75_125_4543 fee75_125_35980 (by decide +kernel)

private theorem tests75_124_4570 : ∀ z∈source124.plan.table,z.1.Valid 75 4570 := by decide +kernel
private theorem fee75_124_35980 :
    PopulationFees20258.bill (n:=35980) (PopulationFees20258.tabulate (35980-1) 256) source124.plan.table+
      4*35980*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*884359728470 := by decide +kernel
private theorem range75From31133To5551 : Segment 75 31133 35980 4570 5551 :=
  paid (pc:=53) (v:=884359728470) (by decide) source124_valid tests75_124_4570 fee75_124_35980 (by decide +kernel)

private theorem range75From31133 : Win 75 31133 35980 :=
  complete (by decide) (by decide) (join_population (join_population range75From31133To4359 range75From31133To4543) (join_population range75From31133To4570 range75From31133To5551))

private theorem fee75_125_39101 :
    PopulationFees20258.bill (n:=39101) (PopulationFees20258.tabulate (39101-1) 256) source125.plan.table+
      4*39101*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*1062036308865 := by decide +kernel
private theorem range75From35981To5301 : Segment 75 35981 39101 0 5301 :=
  paid (pc:=63) (v:=1062036308865) (by decide) source125_valid tests75_125_0 fee75_125_39101 (by decide +kernel)

private theorem tests75_124_5301 : ∀ z∈source124.plan.table,z.1.Valid 75 5301 := by decide +kernel
private theorem fee75_124_39101 :
    PopulationFees20258.bill (n:=39101) (PopulationFees20258.tabulate (39101-1) 256) source124.plan.table+
      4*39101*NaturalPopulation20258.weights source124.extras≤source124.plan.scale*1029501805593 := by decide +kernel
private theorem range75From35981To5541 : Segment 75 35981 39101 5301 5541 :=
  paid (pc:=62) (v:=1029501805593) (by decide) source124_valid tests75_124_5301 fee75_124_39101 (by decide +kernel)

private theorem tests75_124_5541 : ∀ z∈source124.plan.table,z.1.Valid 75 5541 := by decide +kernel
private theorem range75From35981To5551 : Segment 75 35981 39101 5541 5551 :=
  paid (pc:=62) (v:=1029501805593) (by decide) source124_valid tests75_124_5541 fee75_124_39101 (by decide +kernel)

private theorem range75From35981 : Win 75 35981 39101 :=
  complete (by decide) (by decide) (join_population range75From35981To5301 (join_population range75From35981To5541 range75From35981To5551))

private theorem fee75_125_39999 :
    PopulationFees20258.bill (n:=39999) (PopulationFees20258.tabulate (39999-1) 256) source125.plan.table+
      4*39999*NaturalPopulation20258.weights source125.extras≤source125.plan.scale*1106668601675 := by decide +kernel
private theorem range75From39102To5551 : Segment 75 39102 39999 0 5551 :=
  paid (pc:=70) (v:=1106668601675) (by decide) source125_valid tests75_125_0 fee75_125_39999 (by decide +kernel)

private theorem range75From39102 : Win 75 39102 39999 :=
  complete (by decide) (by decide) range75From39102To5551

theorem cut75From20258 : Win 75 20258 39999 :=
  (join_ground (join_ground range75From20258 range75From25265) (join_ground range75From31133 (join_ground range75From35981 range75From39102)))

end JSP233.FiniteCutRanges20258
