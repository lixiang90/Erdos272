module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source094
public import Erdos272.Arithmetic.N20258.Sources.Source096
public import Erdos272.Arithmetic.N20258.Sources.Source097
public import Erdos272.Arithmetic.N20258.Sources.Source098
public import Erdos272.Arithmetic.N20258.Sources.Source099
public import Erdos272.Arithmetic.N20258.Sources.Source100

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests58_098_0 : ∀ z∈source098.plan.table,z.1.Valid 58 0 := by decide +kernel
private theorem fee58_098_24156 :
    PopulationFees20258.bill (n:=24156) (PopulationFees20258.tabulate (24156-1) 256) source098.plan.table+
      4*24156*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*238850257519 := by decide +kernel
private theorem range58From23589To2780 : Segment 58 23589 24156 0 2780 :=
  paid (pc:=76) (v:=238850257519) (by decide) source098_valid tests58_098_0 fee58_098_24156 (by decide +kernel)

private theorem tests58_094_2780 : ∀ z∈source094.plan.table,z.1.Valid 58 2780 := by decide +kernel
private theorem fee58_094_24156 :
    PopulationFees20258.bill (n:=24156) (PopulationFees20258.tabulate (24156-1) 256) source094.plan.table+
      4*24156*NaturalPopulation20258.weights source094.extras≤source094.plan.scale*297696273187 := by decide +kernel
private theorem range58From23589To2833 : Segment 58 23589 24156 2780 2833 :=
  paid (pc:=75) (v:=297696273187) (by decide) source094_valid tests58_094_2780 fee58_094_24156 (by decide +kernel)

private theorem tests58_100_2833 : ∀ z∈source100.plan.table,z.1.Valid 58 2833 := by decide +kernel
private theorem fee58_100_24156 :
    PopulationFees20258.bill (n:=24156) (PopulationFees20258.tabulate (24156-1) 256) source100.plan.table+
      4*24156*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*330735616411 := by decide +kernel
private theorem range58From23589To3036 : Segment 58 23589 24156 2833 3036 :=
  paid (pc:=74) (v:=330735616411) (by decide) source100_valid tests58_100_2833 fee58_100_24156 (by decide +kernel)

private theorem tests58_097_3036 : ∀ z∈source097.plan.table,z.1.Valid 58 3036 := by decide +kernel
private theorem fee58_097_24156 :
    PopulationFees20258.bill (n:=24156) (PopulationFees20258.tabulate (24156-1) 256) source097.plan.table+
      4*24156*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*312018273818 := by decide +kernel
private theorem range58From23589To3159 : Segment 58 23589 24156 3036 3159 :=
  paid (pc:=73) (v:=312018273818) (by decide) source097_valid tests58_097_3036 fee58_097_24156 (by decide +kernel)

private theorem tests58_096_3159 : ∀ z∈source096.plan.table,z.1.Valid 58 3159 := by decide +kernel
private theorem fee58_096_24156 :
    PopulationFees20258.bill (n:=24156) (PopulationFees20258.tabulate (24156-1) 256) source096.plan.table+
      4*24156*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*290049304446 := by decide +kernel
private theorem range58From23589To3304 : Segment 58 23589 24156 3159 3304 :=
  paid (pc:=72) (v:=290049304446) (by decide) source096_valid tests58_096_3159 fee58_096_24156 (by decide +kernel)

private theorem tests58_096_3304 : ∀ z∈source096.plan.table,z.1.Valid 58 3304 := by decide +kernel
private theorem range58From23589To3307 : Segment 58 23589 24156 3304 3307 :=
  paid (pc:=72) (v:=290049304446) (by decide) source096_valid tests58_096_3304 fee58_096_24156 (by decide +kernel)

private theorem range58From23589 : Win 58 23589 24156 :=
  complete (by decide) (by decide) (join_population (join_population range58From23589To2780 (join_population range58From23589To2833 range58From23589To3036)) (join_population range58From23589To3159 (join_population range58From23589To3304 range58From23589To3307)))

private theorem fee58_098_24741 :
    PopulationFees20258.bill (n:=24741) (PopulationFees20258.tabulate (24741-1) 256) source098.plan.table+
      4*24741*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*249492085597 := by decide +kernel
private theorem range58From24157To2815 : Segment 58 24157 24741 0 2815 :=
  paid (pc:=76) (v:=249492085597) (by decide) source098_valid tests58_098_0 fee58_098_24741 (by decide +kernel)

private theorem tests58_100_2815 : ∀ z∈source100.plan.table,z.1.Valid 58 2815 := by decide +kernel
private theorem fee58_100_24741 :
    PopulationFees20258.bill (n:=24741) (PopulationFees20258.tabulate (24741-1) 256) source100.plan.table+
      4*24741*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*345371515179 := by decide +kernel
private theorem range58From24157To3052 : Segment 58 24157 24741 2815 3052 :=
  paid (pc:=74) (v:=345371515179) (by decide) source100_valid tests58_100_2815 fee58_100_24741 (by decide +kernel)

private theorem tests58_097_3052 : ∀ z∈source097.plan.table,z.1.Valid 58 3052 := by decide +kernel
private theorem fee58_097_24741 :
    PopulationFees20258.bill (n:=24741) (PopulationFees20258.tabulate (24741-1) 256) source097.plan.table+
      4*24741*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*325906417621 := by decide +kernel
private theorem range58From24157To3167 : Segment 58 24157 24741 3052 3167 :=
  paid (pc:=73) (v:=325906417621) (by decide) source097_valid tests58_097_3052 fee58_097_24741 (by decide +kernel)

private theorem tests58_096_3167 : ∀ z∈source096.plan.table,z.1.Valid 58 3167 := by decide +kernel
private theorem fee58_096_24741 :
    PopulationFees20258.bill (n:=24741) (PopulationFees20258.tabulate (24741-1) 256) source096.plan.table+
      4*24741*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*303009315643 := by decide +kernel
private theorem range58From24157To3303 : Segment 58 24157 24741 3167 3303 :=
  paid (pc:=72) (v:=303009315643) (by decide) source096_valid tests58_096_3167 fee58_096_24741 (by decide +kernel)

private theorem tests58_096_3303 : ∀ z∈source096.plan.table,z.1.Valid 58 3303 := by decide +kernel
private theorem range58From24157To3307 : Segment 58 24157 24741 3303 3307 :=
  paid (pc:=72) (v:=303009315643) (by decide) source096_valid tests58_096_3303 fee58_096_24741 (by decide +kernel)

private theorem range58From24157 : Win 58 24157 24741 :=
  complete (by decide) (by decide) (join_population (join_population range58From24157To2815 range58From24157To3052) (join_population range58From24157To3167 (join_population range58From24157To3303 range58From24157To3307)))

private theorem fee58_098_25354 :
    PopulationFees20258.bill (n:=25354) (PopulationFees20258.tabulate (25354-1) 256) source098.plan.table+
      4*25354*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*261073925039 := by decide +kernel
private theorem range58From24742To2847 : Segment 58 24742 25354 0 2847 :=
  paid (pc:=76) (v:=261073925039) (by decide) source098_valid tests58_098_0 fee58_098_25354 (by decide +kernel)

private theorem tests58_100_2847 : ∀ z∈source100.plan.table,z.1.Valid 58 2847 := by decide +kernel
private theorem fee58_100_25354 :
    PopulationFees20258.bill (n:=25354) (PopulationFees20258.tabulate (25354-1) 256) source100.plan.table+
      4*25354*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*361239562095 := by decide +kernel
private theorem range58From24742To3066 : Segment 58 24742 25354 2847 3066 :=
  paid (pc:=74) (v:=361239562095) (by decide) source100_valid tests58_100_2847 fee58_100_25354 (by decide +kernel)

private theorem tests58_097_3066 : ∀ z∈source097.plan.table,z.1.Valid 58 3066 := by decide +kernel
private theorem fee58_097_25354 :
    PopulationFees20258.bill (n:=25354) (PopulationFees20258.tabulate (25354-1) 256) source097.plan.table+
      4*25354*NaturalPopulation20258.weights source097.extras≤source097.plan.scale*340947641839 := by decide +kernel
private theorem range58From24742To3176 : Segment 58 24742 25354 3066 3176 :=
  paid (pc:=74) (v:=340947641839) (by decide) source097_valid tests58_097_3066 fee58_097_25354 (by decide +kernel)

private theorem tests58_096_3176 : ∀ z∈source096.plan.table,z.1.Valid 58 3176 := by decide +kernel
private theorem fee58_096_25354 :
    PopulationFees20258.bill (n:=25354) (PopulationFees20258.tabulate (25354-1) 256) source096.plan.table+
      4*25354*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*317047368903 := by decide +kernel
private theorem range58From24742To3303 : Segment 58 24742 25354 3176 3303 :=
  paid (pc:=73) (v:=317047368903) (by decide) source096_valid tests58_096_3176 fee58_096_25354 (by decide +kernel)

private theorem range58From24742To3307 : Segment 58 24742 25354 3303 3307 :=
  paid (pc:=73) (v:=317047368903) (by decide) source096_valid tests58_096_3303 fee58_096_25354 (by decide +kernel)

private theorem range58From24742 : Win 58 24742 25354 :=
  complete (by decide) (by decide) (join_population (join_population range58From24742To2847 range58From24742To3066) (join_population range58From24742To3176 (join_population range58From24742To3303 range58From24742To3307)))

private theorem fee58_098_26013 :
    PopulationFees20258.bill (n:=26013) (PopulationFees20258.tabulate (26013-1) 256) source098.plan.table+
      4*26013*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*273713377670 := by decide +kernel
private theorem range58From25355To2877 : Segment 58 25355 26013 0 2877 :=
  paid (pc:=76) (v:=273713377670) (by decide) source098_valid tests58_098_0 fee58_098_26013 (by decide +kernel)

private theorem tests58_099_2877 : ∀ z∈source099.plan.table,z.1.Valid 58 2877 := by decide +kernel
private theorem fee58_099_26013 :
    PopulationFees20258.bill (n:=26013) (PopulationFees20258.tabulate (26013-1) 256) source099.plan.table+
      4*26013*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*368597502003 := by decide +kernel
private theorem range58From25355To3125 : Segment 58 25355 26013 2877 3125 :=
  paid (pc:=74) (v:=368597502003) (by decide) source099_valid tests58_099_2877 fee58_099_26013 (by decide +kernel)

private theorem tests58_096_3125 : ∀ z∈source096.plan.table,z.1.Valid 58 3125 := by decide +kernel
private theorem fee58_096_26013 :
    PopulationFees20258.bill (n:=26013) (PopulationFees20258.tabulate (26013-1) 256) source096.plan.table+
      4*26013*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*332351618672 := by decide +kernel
private theorem range58From25355To3302 : Segment 58 25355 26013 3125 3302 :=
  paid (pc:=73) (v:=332351618672) (by decide) source096_valid tests58_096_3125 fee58_096_26013 (by decide +kernel)

private theorem tests58_096_3302 : ∀ z∈source096.plan.table,z.1.Valid 58 3302 := by decide +kernel
private theorem range58From25355To3307 : Segment 58 25355 26013 3302 3307 :=
  paid (pc:=73) (v:=332351618672) (by decide) source096_valid tests58_096_3302 fee58_096_26013 (by decide +kernel)

private theorem range58From25355 : Win 58 25355 26013 :=
  complete (by decide) (by decide) (join_population (join_population range58From25355To2877 range58From25355To3125) (join_population range58From25355To3302 range58From25355To3307))

private theorem fee58_098_26732 :
    PopulationFees20258.bill (n:=26732) (PopulationFees20258.tabulate (26732-1) 256) source098.plan.table+
      4*26732*NaturalPopulation20258.weights source098.extras≤source098.plan.scale*287921530452 := by decide +kernel
private theorem range58From26014To2907 : Segment 58 26014 26732 0 2907 :=
  paid (pc:=76) (v:=287921530452) (by decide) source098_valid tests58_098_0 fee58_098_26732 (by decide +kernel)

private theorem tests58_099_2907 : ∀ z∈source099.plan.table,z.1.Valid 58 2907 := by decide +kernel
private theorem fee58_099_26732 :
    PopulationFees20258.bill (n:=26732) (PopulationFees20258.tabulate (26732-1) 256) source099.plan.table+
      4*26732*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*387601378406 := by decide +kernel
private theorem range58From26014To3136 : Segment 58 26014 26732 2907 3136 :=
  paid (pc:=75) (v:=387601378406) (by decide) source099_valid tests58_099_2907 fee58_099_26732 (by decide +kernel)

private theorem tests58_096_3136 : ∀ z∈source096.plan.table,z.1.Valid 58 3136 := by decide +kernel
private theorem fee58_096_26732 :
    PopulationFees20258.bill (n:=26732) (PopulationFees20258.tabulate (26732-1) 256) source096.plan.table+
      4*26732*NaturalPopulation20258.weights source096.extras≤source096.plan.scale*349755681725 := by decide +kernel
private theorem range58From26014To3304 : Segment 58 26014 26732 3136 3304 :=
  paid (pc:=74) (v:=349755681725) (by decide) source096_valid tests58_096_3136 fee58_096_26732 (by decide +kernel)

private theorem range58From26014To3307 : Segment 58 26014 26732 3304 3307 :=
  paid (pc:=74) (v:=349755681725) (by decide) source096_valid tests58_096_3304 fee58_096_26732 (by decide +kernel)

private theorem range58From26014 : Win 58 26014 26732 :=
  complete (by decide) (by decide) (join_population (join_population range58From26014To2907 range58From26014To3136) (join_population range58From26014To3304 range58From26014To3307))

theorem cut58From23589 : Win 58 23589 26732 :=
  (join_ground (join_ground range58From23589 range58From24157) (join_ground range58From24742 (join_ground range58From25355 range58From26014)))

end JSP233.FiniteCutRanges20258
