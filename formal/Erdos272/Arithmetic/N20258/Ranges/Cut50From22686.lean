module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source018
public import Erdos272.Arithmetic.N20258.Sources.Source026
public import Erdos272.Arithmetic.N20258.Sources.Source028
public import Erdos272.Arithmetic.N20258.Sources.Source031
public import Erdos272.Arithmetic.N20258.Sources.Source033
public import Erdos272.Arithmetic.N20258.Sources.Source035

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests50_028_0 : ∀ z∈source028.plan.table,z.1.Valid 50 0 := by decide +kernel
private theorem fee50_028_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source028.plan.table+
      4*23360*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*114457997418 := by decide +kernel
private theorem range50From22686To2237 : Segment 50 22686 23360 0 2237 :=
  paid (pc:=78) (v:=114457997418) (by decide) source028_valid tests50_028_0 fee50_028_23360 (by decide +kernel)

private theorem tests50_018_2237 : ∀ z∈source018.plan.table,z.1.Valid 50 2237 := by decide +kernel
private theorem fee50_018_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source018.plan.table+
      4*23360*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*199946382276 := by decide +kernel
private theorem range50From22686To2307 : Segment 50 22686 23360 2237 2307 :=
  paid (pc:=78) (v:=199946382276) (by decide) source018_valid tests50_018_2237 fee50_018_23360 (by decide +kernel)

private theorem tests50_031_2307 : ∀ z∈source031.plan.table,z.1.Valid 50 2307 := by decide +kernel
private theorem fee50_031_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source031.plan.table+
      4*23360*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*189419834703 := by decide +kernel
private theorem range50From22686To2349 : Segment 50 22686 23360 2307 2349 :=
  paid (pc:=78) (v:=189419834703) (by decide) source031_valid tests50_031_2307 fee50_031_23360 (by decide +kernel)

private theorem tests50_033_2349 : ∀ z∈source033.plan.table,z.1.Valid 50 2349 := by decide +kernel
private theorem fee50_033_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source033.plan.table+
      4*23360*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*233310148151 := by decide +kernel
private theorem range50From22686To2391 : Segment 50 22686 23360 2349 2391 :=
  paid (pc:=77) (v:=233310148151) (by decide) source033_valid tests50_033_2349 fee50_033_23360 (by decide +kernel)

private theorem tests50_026_2391 : ∀ z∈source026.plan.table,z.1.Valid 50 2391 := by decide +kernel
private theorem fee50_026_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source026.plan.table+
      4*23360*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*230089243130 := by decide +kernel
private theorem range50From22686To2406 : Segment 50 22686 23360 2391 2406 :=
  paid (pc:=77) (v:=230089243130) (by decide) source026_valid tests50_026_2391 fee50_026_23360 (by decide +kernel)

private theorem tests50_035_2406 : ∀ z∈source035.plan.table,z.1.Valid 50 2406 := by decide +kernel
private theorem fee50_035_23360 :
    PopulationFees20258.bill (n:=23360) (PopulationFees20258.tabulate (23360-1) 256) source035.plan.table+
      4*23360*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*219867751885 := by decide +kernel
private theorem range50From22686To2451 : Segment 50 22686 23360 2406 2451 :=
  paid (pc:=77) (v:=219867751885) (by decide) source035_valid tests50_035_2406 fee50_035_23360 (by decide +kernel)

private theorem range50From22686 : Win 50 22686 23360 :=
  complete (by decide) (by decide) (join_population (join_population range50From22686To2237 (join_population range50From22686To2307 range50From22686To2349)) (join_population range50From22686To2391 (join_population range50From22686To2406 range50From22686To2451)))

private theorem fee50_028_24192 :
    PopulationFees20258.bill (n:=24192) (PopulationFees20258.tabulate (24192-1) 256) source028.plan.table+
      4*24192*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*122261625105 := by decide +kernel
private theorem range50From23361To2258 : Segment 50 23361 24192 0 2258 :=
  paid (pc:=78) (v:=122261625105) (by decide) source028_valid tests50_028_0 fee50_028_24192 (by decide +kernel)

private theorem tests50_031_2258 : ∀ z∈source031.plan.table,z.1.Valid 50 2258 := by decide +kernel
private theorem fee50_031_24192 :
    PopulationFees20258.bill (n:=24192) (PopulationFees20258.tabulate (24192-1) 256) source031.plan.table+
      4*24192*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*202187917880 := by decide +kernel
private theorem range50From23361To2357 : Segment 50 23361 24192 2258 2357 :=
  paid (pc:=77) (v:=202187917880) (by decide) source031_valid tests50_031_2258 fee50_031_24192 (by decide +kernel)

private theorem tests50_033_2357 : ∀ z∈source033.plan.table,z.1.Valid 50 2357 := by decide +kernel
private theorem fee50_033_24192 :
    PopulationFees20258.bill (n:=24192) (PopulationFees20258.tabulate (24192-1) 256) source033.plan.table+
      4*24192*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*248952086684 := by decide +kernel
private theorem range50From23361To2395 : Segment 50 23361 24192 2357 2395 :=
  paid (pc:=77) (v:=248952086684) (by decide) source033_valid tests50_033_2357 fee50_033_24192 (by decide +kernel)

private theorem tests50_026_2395 : ∀ z∈source026.plan.table,z.1.Valid 50 2395 := by decide +kernel
private theorem fee50_026_24192 :
    PopulationFees20258.bill (n:=24192) (PopulationFees20258.tabulate (24192-1) 256) source026.plan.table+
      4*24192*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*245515353040 := by decide +kernel
private theorem range50From23361To2408 : Segment 50 23361 24192 2395 2408 :=
  paid (pc:=77) (v:=245515353040) (by decide) source026_valid tests50_026_2395 fee50_026_24192 (by decide +kernel)

private theorem tests50_035_2408 : ∀ z∈source035.plan.table,z.1.Valid 50 2408 := by decide +kernel
private theorem fee50_035_24192 :
    PopulationFees20258.bill (n:=24192) (PopulationFees20258.tabulate (24192-1) 256) source035.plan.table+
      4*24192*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*234664364205 := by decide +kernel
private theorem range50From23361To2451 : Segment 50 23361 24192 2408 2451 :=
  paid (pc:=77) (v:=234664364205) (by decide) source035_valid tests50_035_2408 fee50_035_24192 (by decide +kernel)

private theorem range50From23361 : Win 50 23361 24192 :=
  complete (by decide) (by decide) (join_population (join_population range50From23361To2258 range50From23361To2357) (join_population range50From23361To2395 (join_population range50From23361To2408 range50From23361To2451)))

private theorem fee50_028_25234 :
    PopulationFees20258.bill (n:=25234) (PopulationFees20258.tabulate (25234-1) 256) source028.plan.table+
      4*25234*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*132460124942 := by decide +kernel
private theorem range50From24193To2280 : Segment 50 24193 25234 0 2280 :=
  paid (pc:=78) (v:=132460124942) (by decide) source028_valid tests50_028_0 fee50_028_25234 (by decide +kernel)

private theorem tests50_031_2280 : ∀ z∈source031.plan.table,z.1.Valid 50 2280 := by decide +kernel
private theorem fee50_031_25234 :
    PopulationFees20258.bill (n:=25234) (PopulationFees20258.tabulate (25234-1) 256) source031.plan.table+
      4*25234*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*218854175935 := by decide +kernel
private theorem range50From24193To2366 : Segment 50 24193 25234 2280 2366 :=
  paid (pc:=77) (v:=218854175935) (by decide) source031_valid tests50_031_2280 fee50_031_25234 (by decide +kernel)

private theorem tests50_033_2366 : ∀ z∈source033.plan.table,z.1.Valid 50 2366 := by decide +kernel
private theorem fee50_033_25234 :
    PopulationFees20258.bill (n:=25234) (PopulationFees20258.tabulate (25234-1) 256) source033.plan.table+
      4*25234*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*269342453536 := by decide +kernel
private theorem range50From24193To2396 : Segment 50 24193 25234 2366 2396 :=
  paid (pc:=77) (v:=269342453536) (by decide) source033_valid tests50_033_2366 fee50_033_25234 (by decide +kernel)

private theorem tests50_026_2396 : ∀ z∈source026.plan.table,z.1.Valid 50 2396 := by decide +kernel
private theorem fee50_026_25234 :
    PopulationFees20258.bill (n:=25234) (PopulationFees20258.tabulate (25234-1) 256) source026.plan.table+
      4*25234*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*265677419425 := by decide +kernel
private theorem range50From24193To2409 : Segment 50 24193 25234 2396 2409 :=
  paid (pc:=77) (v:=265677419425) (by decide) source026_valid tests50_026_2396 fee50_026_25234 (by decide +kernel)

private theorem tests50_035_2409 : ∀ z∈source035.plan.table,z.1.Valid 50 2409 := by decide +kernel
private theorem fee50_035_25234 :
    PopulationFees20258.bill (n:=25234) (PopulationFees20258.tabulate (25234-1) 256) source035.plan.table+
      4*25234*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*253973890611 := by decide +kernel
private theorem range50From24193To2451 : Segment 50 24193 25234 2409 2451 :=
  paid (pc:=77) (v:=253973890611) (by decide) source035_valid tests50_035_2409 fee50_035_25234 (by decide +kernel)

private theorem range50From24193 : Win 50 24193 25234 :=
  complete (by decide) (by decide) (join_population (join_population range50From24193To2280 range50From24193To2366) (join_population range50From24193To2396 (join_population range50From24193To2409 range50From24193To2451)))

private theorem fee50_028_26560 :
    PopulationFees20258.bill (n:=26560) (PopulationFees20258.tabulate (26560-1) 256) source028.plan.table+
      4*26560*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*146017476341 := by decide +kernel
private theorem range50From25235To2306 : Segment 50 25235 26560 0 2306 :=
  paid (pc:=77) (v:=146017476341) (by decide) source028_valid tests50_028_0 fee50_028_26560 (by decide +kernel)

private theorem tests50_031_2306 : ∀ z∈source031.plan.table,z.1.Valid 50 2306 := by decide +kernel
private theorem fee50_031_26560 :
    PopulationFees20258.bill (n:=26560) (PopulationFees20258.tabulate (26560-1) 256) source031.plan.table+
      4*26560*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*240985419728 := by decide +kernel
private theorem range50From25235To2378 : Segment 50 25235 26560 2306 2378 :=
  paid (pc:=77) (v:=240985419728) (by decide) source031_valid tests50_031_2306 fee50_031_26560 (by decide +kernel)

private theorem tests50_033_2378 : ∀ z∈source033.plan.table,z.1.Valid 50 2378 := by decide +kernel
private theorem fee50_033_26560 :
    PopulationFees20258.bill (n:=26560) (PopulationFees20258.tabulate (26560-1) 256) source033.plan.table+
      4*26560*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*296428925040 := by decide +kernel
private theorem range50From25235To2398 : Segment 50 25235 26560 2378 2398 :=
  paid (pc:=77) (v:=296428925040) (by decide) source033_valid tests50_033_2378 fee50_033_26560 (by decide +kernel)

private theorem tests50_026_2398 : ∀ z∈source026.plan.table,z.1.Valid 50 2398 := by decide +kernel
private theorem fee50_026_26560 :
    PopulationFees20258.bill (n:=26560) (PopulationFees20258.tabulate (26560-1) 256) source026.plan.table+
      4*26560*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*292496551626 := by decide +kernel
private theorem range50From25235To2410 : Segment 50 25235 26560 2398 2410 :=
  paid (pc:=76) (v:=292496551626) (by decide) source026_valid tests50_026_2398 fee50_026_26560 (by decide +kernel)

private theorem tests50_035_2410 : ∀ z∈source035.plan.table,z.1.Valid 50 2410 := by decide +kernel
private theorem fee50_035_26560 :
    PopulationFees20258.bill (n:=26560) (PopulationFees20258.tabulate (26560-1) 256) source035.plan.table+
      4*26560*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*279583747560 := by decide +kernel
private theorem range50From25235To2451 : Segment 50 25235 26560 2410 2451 :=
  paid (pc:=76) (v:=279583747560) (by decide) source035_valid tests50_035_2410 fee50_035_26560 (by decide +kernel)

private theorem range50From25235 : Win 50 25235 26560 :=
  complete (by decide) (by decide) (join_population (join_population range50From25235To2306 range50From25235To2378) (join_population range50From25235To2398 (join_population range50From25235To2410 range50From25235To2451)))

theorem cut50From22686 : Win 50 22686 26560 :=
  (join_ground (join_ground range50From22686 range50From23361) (join_ground range50From24193 range50From25235))

end JSP233.FiniteCutRanges20258
