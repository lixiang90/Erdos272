module

public import Erdos272.Arithmetic.N20258.Sources.Source097
public import Erdos272.Arithmetic.N20258.Sources.Source099
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source104
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee83At20052 :
    PopulationFees20258.bill (n:=20052) (PopulationFees20258.tabulate (20052-1) 256) PopulationSources20258.source104.plan.table+
      4*20052*NaturalPopulation20258.weights PopulationSources20258.source104.extras≤PopulationSources20258.source104.plan.scale*145816520794 := by decide +kernel
private theorem from19683To2867 : Segment 60 19683 20052 0 2867 :=
  paid (pc:=71) (v:=145816520794) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At20052 (by decide +kernel)

private theorem from19683To2902 : Segment 60 19683 20052 2867 2902 :=
  paid (pc:=71) (v:=145816520794) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At20052 (by decide +kernel)

private theorem from19683To2904 : Segment 60 19683 20052 2902 2904 :=
  paid (pc:=71) (v:=145816520794) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At20052 (by decide +kernel)

private theorem fee80At20052 :
    PopulationFees20258.bill (n:=20052) (PopulationFees20258.tabulate (20052-1) 256) PopulationSources20258.source100.plan.table+
      4*20052*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*236379213965 := by decide +kernel
private theorem from19683To3325 : Segment 60 19683 20052 2904 3325 :=
  paid (pc:=67) (v:=236379213965) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At20052 (by decide +kernel)

private theorem fee78At20052 :
    PopulationFees20258.bill (n:=20052) (PopulationFees20258.tabulate (20052-1) 256) PopulationSources20258.source097.plan.table+
      4*20052*NaturalPopulation20258.weights PopulationSources20258.source097.extras≤PopulationSources20258.source097.plan.scale*222517010056 := by decide +kernel
private theorem from19683To3541 : Segment 60 19683 20052 3325 3541 :=
  paid (pc:=59) (v:=222517010056) (by decide) PopulationSources20258.source097_valid (by decide +kernel) fee78At20052 (by decide +kernel)

private theorem range19683 : Win 60 19683 20052 :=
  complete (by decide) (by decide) (join_population (join_population from19683To2867 from19683To2902) (join_population from19683To2904 (join_population from19683To3325 from19683To3541)))

private theorem fee83At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source104.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source104.extras≤PopulationSources20258.source104.plan.scale*148607042404 := by decide +kernel
private theorem from20053To2953 : Segment 60 20053 20257 0 2953 :=
  paid (pc:=72) (v:=148607042404) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At20257 (by decide +kernel)

private theorem fee145At20257 :
    PopulationFees20258.bill (n:=20257) (PopulationFees20258.tabulate (20257-1) 256) PopulationSources20258.source099.plan.table+
      4*20257*NaturalPopulation20258.weights PopulationSources20258.source099.extras≤PopulationSources20258.source099.plan.scale*234250372309 := by decide +kernel
private theorem from20053To3541 : Segment 60 20053 20257 2953 3541 :=
  paid (pc:=65) (v:=234250372309) (by decide) PopulationSources20258.source099_valid (by decide +kernel) fee145At20257 (by decide +kernel)

private theorem range20053 : Win 60 20053 20257 :=
  complete (by decide) (by decide) (join_population from20053To2953 from20053To3541)

theorem bridge60 : Win 60 19683 20257 :=
  (join_ground range19683 range20053)

end JSP233.Credit19227
