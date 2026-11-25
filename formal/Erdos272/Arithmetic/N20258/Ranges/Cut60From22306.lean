module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source099
public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source102
public import Erdos272.Arithmetic.N20258.Sources.Source104
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests60_104_0 : ∀ z∈source104.plan.table,z.1.Valid 60 0 := by decide +kernel
private theorem fee60_104_22816 :
    PopulationFees20258.bill (n:=22816) (PopulationFees20258.tabulate (22816-1) 256) source104.plan.table+
      4*22816*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*184634890194 := by decide +kernel
private theorem range60From22306To2881 : Segment 60 22306 22816 0 2881 :=
  paid (pc:=74) (v:=184634890194) (by decide) source104_valid tests60_104_0 fee60_104_22816 (by decide +kernel)

private theorem tests60_104_2881 : ∀ z∈source104.plan.table,z.1.Valid 60 2881 := by decide +kernel
private theorem range60From22306To2903 : Segment 60 22306 22816 2881 2903 :=
  paid (pc:=74) (v:=184634890194) (by decide) source104_valid tests60_104_2881 fee60_104_22816 (by decide +kernel)

private theorem tests60_104_2903 : ∀ z∈source104.plan.table,z.1.Valid 60 2903 := by decide +kernel
private theorem range60From22306To2904 : Segment 60 22306 22816 2903 2904 :=
  paid (pc:=74) (v:=184634890194) (by decide) source104_valid tests60_104_2903 fee60_104_22816 (by decide +kernel)

private theorem tests60_100_2904 : ∀ z∈source100.plan.table,z.1.Valid 60 2904 := by decide +kernel
private theorem fee60_100_22816 :
    PopulationFees20258.bill (n:=22816) (PopulationFees20258.tabulate (22816-1) 256) source100.plan.table+
      4*22816*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*298225292004 := by decide +kernel
private theorem range60From22306To3029 : Segment 60 22306 22816 2904 3029 :=
  paid (pc:=73) (v:=298225292004) (by decide) source100_valid tests60_100_2904 fee60_100_22816 (by decide +kernel)

private theorem tests60_106_3029 : ∀ z∈source106.plan.table,z.1.Valid 60 3029 := by decide +kernel
private theorem fee60_106_22816 :
    PopulationFees20258.bill (n:=22816) (PopulationFees20258.tabulate (22816-1) 256) source106.plan.table+
      4*22816*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*310059517319 := by decide +kernel
private theorem range60From22306To3541 : Segment 60 22306 22816 3029 3541 :=
  paid (pc:=68) (v:=310059517319) (by decide) source106_valid tests60_106_3029 fee60_106_22816 (by decide +kernel)

private theorem range60From22306 : Win 60 22306 22816 :=
  complete (by decide) (by decide) (join_population (join_population range60From22306To2881 range60From22306To2903) (join_population range60From22306To2904 (join_population range60From22306To3029 range60From22306To3541)))

private theorem fee60_104_23391 :
    PopulationFees20258.bill (n:=23391) (PopulationFees20258.tabulate (23391-1) 256) source104.plan.table+
      4*23391*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*193251160997 := by decide +kernel
private theorem range60From22817To2881 : Segment 60 22817 23391 0 2881 :=
  paid (pc:=74) (v:=193251160997) (by decide) source104_valid tests60_104_0 fee60_104_23391 (by decide +kernel)

private theorem range60From22817To2902 : Segment 60 22817 23391 2881 2902 :=
  paid (pc:=74) (v:=193251160997) (by decide) source104_valid tests60_104_2881 fee60_104_23391 (by decide +kernel)

private theorem tests60_104_2902 : ∀ z∈source104.plan.table,z.1.Valid 60 2902 := by decide +kernel
private theorem range60From22817To2904 : Segment 60 22817 23391 2902 2904 :=
  paid (pc:=74) (v:=193251160997) (by decide) source104_valid tests60_104_2902 fee60_104_23391 (by decide +kernel)

private theorem fee60_100_23391 :
    PopulationFees20258.bill (n:=23391) (PopulationFees20258.tabulate (23391-1) 256) source100.plan.table+
      4*23391*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*311868278285 := by decide +kernel
private theorem range60From22817To3004 : Segment 60 22817 23391 2904 3004 :=
  paid (pc:=73) (v:=311868278285) (by decide) source100_valid tests60_100_2904 fee60_100_23391 (by decide +kernel)

private theorem tests60_102_3004 : ∀ z∈source102.plan.table,z.1.Valid 60 3004 := by decide +kernel
private theorem fee60_102_23391 :
    PopulationFees20258.bill (n:=23391) (PopulationFees20258.tabulate (23391-1) 256) source102.plan.table+
      4*23391*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*283919551511 := by decide +kernel
private theorem range60From22817To3208 : Segment 60 22817 23391 3004 3208 :=
  paid (pc:=71) (v:=283919551511) (by decide) source102_valid tests60_102_3004 fee60_102_23391 (by decide +kernel)

private theorem tests60_105_3208 : ∀ z∈source105.plan.table,z.1.Valid 60 3208 := by decide +kernel
private theorem fee60_105_23391 :
    PopulationFees20258.bill (n:=23391) (PopulationFees20258.tabulate (23391-1) 256) source105.plan.table+
      4*23391*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*317932679366 := by decide +kernel
private theorem range60From22817To3541 : Segment 60 22817 23391 3208 3541 :=
  paid (pc:=68) (v:=317932679366) (by decide) source105_valid tests60_105_3208 fee60_105_23391 (by decide +kernel)

private theorem range60From22817 : Win 60 22817 23391 :=
  complete (by decide) (by decide) (join_population (join_population range60From22817To2881 (join_population range60From22817To2902 range60From22817To2904)) (join_population range60From22817To3004 (join_population range60From22817To3208 range60From22817To3541)))

private theorem fee60_104_24012 :
    PopulationFees20258.bill (n:=24012) (PopulationFees20258.tabulate (24012-1) 256) source104.plan.table+
      4*24012*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*202700970446 := by decide +kernel
private theorem range60From23392To2897 : Segment 60 23392 24012 0 2897 :=
  paid (pc:=74) (v:=202700970446) (by decide) source104_valid tests60_104_0 fee60_104_24012 (by decide +kernel)

private theorem tests60_104_2897 : ∀ z∈source104.plan.table,z.1.Valid 60 2897 := by decide +kernel
private theorem range60From23392To2918 : Segment 60 23392 24012 2897 2918 :=
  paid (pc:=74) (v:=202700970446) (by decide) source104_valid tests60_104_2897 fee60_104_24012 (by decide +kernel)

private theorem tests60_100_2918 : ∀ z∈source100.plan.table,z.1.Valid 60 2918 := by decide +kernel
private theorem fee60_100_24012 :
    PopulationFees20258.bill (n:=24012) (PopulationFees20258.tabulate (24012-1) 256) source100.plan.table+
      4*24012*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*327143220264 := by decide +kernel
private theorem range60From23392To2997 : Segment 60 23392 24012 2918 2997 :=
  paid (pc:=74) (v:=327143220264) (by decide) source100_valid tests60_100_2918 fee60_100_24012 (by decide +kernel)

private theorem tests60_102_2997 : ∀ z∈source102.plan.table,z.1.Valid 60 2997 := by decide +kernel
private theorem fee60_102_24012 :
    PopulationFees20258.bill (n:=24012) (PopulationFees20258.tabulate (24012-1) 256) source102.plan.table+
      4*24012*NaturalPopulation20258.weights source102.extras≤source102.plan.scale*297874767789 := by decide +kernel
private theorem range60From23392To3187 : Segment 60 23392 24012 2997 3187 :=
  paid (pc:=72) (v:=297874767789) (by decide) source102_valid tests60_102_2997 fee60_102_24012 (by decide +kernel)

private theorem tests60_105_3187 : ∀ z∈source105.plan.table,z.1.Valid 60 3187 := by decide +kernel
private theorem fee60_105_24012 :
    PopulationFees20258.bill (n:=24012) (PopulationFees20258.tabulate (24012-1) 256) source105.plan.table+
      4*24012*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*333210542448 := by decide +kernel
private theorem range60From23392To3529 : Segment 60 23392 24012 3187 3529 :=
  paid (pc:=69) (v:=333210542448) (by decide) source105_valid tests60_105_3187 fee60_105_24012 (by decide +kernel)

private theorem tests60_105_3529 : ∀ z∈source105.plan.table,z.1.Valid 60 3529 := by decide +kernel
private theorem range60From23392To3541 : Segment 60 23392 24012 3529 3541 :=
  paid (pc:=69) (v:=333210542448) (by decide) source105_valid tests60_105_3529 fee60_105_24012 (by decide +kernel)

private theorem range60From23392 : Win 60 23392 24012 :=
  complete (by decide) (by decide) (join_population (join_population range60From23392To2897 (join_population range60From23392To2918 range60From23392To2997)) (join_population range60From23392To3187 (join_population range60From23392To3529 range60From23392To3541)))

private theorem fee60_104_24592 :
    PopulationFees20258.bill (n:=24592) (PopulationFees20258.tabulate (24592-1) 256) source104.plan.table+
      4*24592*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*211796696051 := by decide +kernel
private theorem range60From24013To2952 : Segment 60 24013 24592 0 2952 :=
  paid (pc:=75) (v:=211796696051) (by decide) source104_valid tests60_104_0 fee60_104_24592 (by decide +kernel)

private theorem tests60_099_2952 : ∀ z∈source099.plan.table,z.1.Valid 60 2952 := by decide +kernel
private theorem fee60_099_24592 :
    PopulationFees20258.bill (n:=24592) (PopulationFees20258.tabulate (24592-1) 256) source099.plan.table+
      4*24592*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*332708772346 := by decide +kernel
private theorem range60From24013To3097 : Segment 60 24013 24592 2952 3097 :=
  paid (pc:=74) (v:=332708772346) (by decide) source099_valid tests60_099_2952 fee60_099_24592 (by decide +kernel)

private theorem tests60_105_3097 : ∀ z∈source105.plan.table,z.1.Valid 60 3097 := by decide +kernel
private theorem fee60_105_24592 :
    PopulationFees20258.bill (n:=24592) (PopulationFees20258.tabulate (24592-1) 256) source105.plan.table+
      4*24592*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*347959765161 := by decide +kernel
private theorem range60From24013To3525 : Segment 60 24013 24592 3097 3525 :=
  paid (pc:=70) (v:=347959765161) (by decide) source105_valid tests60_105_3097 fee60_105_24592 (by decide +kernel)

private theorem tests60_105_3525 : ∀ z∈source105.plan.table,z.1.Valid 60 3525 := by decide +kernel
private theorem range60From24013To3541 : Segment 60 24013 24592 3525 3541 :=
  paid (pc:=70) (v:=347959765161) (by decide) source105_valid tests60_105_3525 fee60_105_24592 (by decide +kernel)

private theorem range60From24013 : Win 60 24013 24592 :=
  complete (by decide) (by decide) (join_population (join_population range60From24013To2952 range60From24013To3097) (join_population range60From24013To3525 range60From24013To3541))

theorem cut60From22306 : Win 60 22306 24592 :=
  (join_ground (join_ground range60From22306 range60From22817) (join_ground range60From23392 range60From24013))

end JSP233.FiniteCutRanges20258
