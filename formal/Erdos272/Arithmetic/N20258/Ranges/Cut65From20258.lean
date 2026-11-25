module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source108
public import Erdos272.Arithmetic.N20258.Sources.Source112
public import Erdos272.Arithmetic.N20258.Sources.Source115
public import Erdos272.Arithmetic.N20258.Sources.Source116

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests65_116_0 : ∀ z∈source116.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_116_21696 :
    PopulationFees20258.bill (n:=21696) (PopulationFees20258.tabulate (21696-1) 256) source116.plan.table+
      4*21696*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*188129702705 := by decide +kernel
private theorem range65From20258To3501 : Segment 65 20258 21696 0 3501 :=
  paid (pc:=60) (v:=188129702705) (by decide) source116_valid tests65_116_0 fee65_116_21696 (by decide +kernel)

private theorem tests65_116_3501 : ∀ z∈source116.plan.table,z.1.Valid 65 3501 := by decide +kernel
private theorem range65From20258To3630 : Segment 65 20258 21696 3501 3630 :=
  paid (pc:=58) (v:=188129702705) (by decide) source116_valid tests65_116_3501 fee65_116_21696 (by decide +kernel)

private theorem tests65_116_3630 : ∀ z∈source116.plan.table,z.1.Valid 65 3630 := by decide +kernel
private theorem range65From20258To3641 : Segment 65 20258 21696 3630 3641 :=
  paid (pc:=58) (v:=188129702705) (by decide) source116_valid tests65_116_3630 fee65_116_21696 (by decide +kernel)

private theorem tests65_108_3641 : ∀ z∈source108.plan.table,z.1.Valid 65 3641 := by decide +kernel
private theorem fee65_108_21696 :
    PopulationFees20258.bill (n:=21696) (PopulationFees20258.tabulate (21696-1) 256) source108.plan.table+
      4*21696*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*228259293900 := by decide +kernel
private theorem range65From20258To4161 : Segment 65 20258 21696 3641 4161 :=
  paid (pc:=55) (v:=228259293900) (by decide) source108_valid tests65_108_3641 fee65_108_21696 (by decide +kernel)

private theorem range65From20258 : Win 65 20258 21696 :=
  complete (by decide) (by decide) (join_population (join_population range65From20258To3501 range65From20258To3630) (join_population range65From20258To3641 range65From20258To4161))

private theorem fee65_116_22680 :
    PopulationFees20258.bill (n:=22680) (PopulationFees20258.tabulate (22680-1) 256) source116.plan.table+
      4*22680*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*203815738023 := by decide +kernel
private theorem range65From21697To3567 : Segment 65 21697 22680 0 3567 :=
  paid (pc:=64) (v:=203815738023) (by decide) source116_valid tests65_116_0 fee65_116_22680 (by decide +kernel)

private theorem tests65_116_3567 : ∀ z∈source116.plan.table,z.1.Valid 65 3567 := by decide +kernel
private theorem range65From21697To3639 : Segment 65 21697 22680 3567 3639 :=
  paid (pc:=64) (v:=203815738023) (by decide) source116_valid tests65_116_3567 fee65_116_22680 (by decide +kernel)

private theorem tests65_108_3639 : ∀ z∈source108.plan.table,z.1.Valid 65 3639 := by decide +kernel
private theorem fee65_108_22680 :
    PopulationFees20258.bill (n:=22680) (PopulationFees20258.tabulate (22680-1) 256) source108.plan.table+
      4*22680*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*247332496204 := by decide +kernel
private theorem range65From21697To4161 : Segment 65 21697 22680 3639 4161 :=
  paid (pc:=58) (v:=247332496204) (by decide) source108_valid tests65_108_3639 fee65_108_22680 (by decide +kernel)

private theorem range65From21697 : Win 65 21697 22680 :=
  complete (by decide) (by decide) (join_population range65From21697To3567 (join_population range65From21697To3639 range65From21697To4161))

private theorem fee65_116_23490 :
    PopulationFees20258.bill (n:=23490) (PopulationFees20258.tabulate (23490-1) 256) source116.plan.table+
      4*23490*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*217287400697 := by decide +kernel
private theorem range65From22681To3582 : Segment 65 22681 23490 0 3582 :=
  paid (pc:=67) (v:=217287400697) (by decide) source116_valid tests65_116_0 fee65_116_23490 (by decide +kernel)

private theorem tests65_116_3582 : ∀ z∈source116.plan.table,z.1.Valid 65 3582 := by decide +kernel
private theorem range65From22681To3637 : Segment 65 22681 23490 3582 3637 :=
  paid (pc:=66) (v:=217287400697) (by decide) source116_valid tests65_116_3582 fee65_116_23490 (by decide +kernel)

private theorem tests65_116_3637 : ∀ z∈source116.plan.table,z.1.Valid 65 3637 := by decide +kernel
private theorem range65From22681To3639 : Segment 65 22681 23490 3637 3639 :=
  paid (pc:=66) (v:=217287400697) (by decide) source116_valid tests65_116_3637 fee65_116_23490 (by decide +kernel)

private theorem fee65_108_23490 :
    PopulationFees20258.bill (n:=23490) (PopulationFees20258.tabulate (23490-1) 256) source108.plan.table+
      4*23490*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*263795574807 := by decide +kernel
private theorem range65From22681To4161 : Segment 65 22681 23490 3639 4161 :=
  paid (pc:=62) (v:=263795574807) (by decide) source108_valid tests65_108_3639 fee65_108_23490 (by decide +kernel)

private theorem range65From22681 : Win 65 22681 23490 :=
  complete (by decide) (by decide) (join_population (join_population range65From22681To3582 range65From22681To3637) (join_population range65From22681To3639 range65From22681To4161))

private theorem fee65_116_24212 :
    PopulationFees20258.bill (n:=24212) (PopulationFees20258.tabulate (24212-1) 256) source116.plan.table+
      4*24212*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*229775068567 := by decide +kernel
private theorem range65From23491To3590 : Segment 65 23491 24212 0 3590 :=
  paid (pc:=68) (v:=229775068567) (by decide) source116_valid tests65_116_0 fee65_116_24212 (by decide +kernel)

private theorem tests65_116_3590 : ∀ z∈source116.plan.table,z.1.Valid 65 3590 := by decide +kernel
private theorem range65From23491To3639 : Segment 65 23491 24212 3590 3639 :=
  paid (pc:=68) (v:=229775068567) (by decide) source116_valid tests65_116_3590 fee65_116_24212 (by decide +kernel)

private theorem fee65_108_24212 :
    PopulationFees20258.bill (n:=24212) (PopulationFees20258.tabulate (24212-1) 256) source108.plan.table+
      4*24212*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*278810779716 := by decide +kernel
private theorem range65From23491To4018 : Segment 65 23491 24212 3639 4018 :=
  paid (pc:=65) (v:=278810779716) (by decide) source108_valid tests65_108_3639 fee65_108_24212 (by decide +kernel)

private theorem tests65_112_4018 : ∀ z∈source112.plan.table,z.1.Valid 65 4018 := by decide +kernel
private theorem fee65_112_24212 :
    PopulationFees20258.bill (n:=24212) (PopulationFees20258.tabulate (24212-1) 256) source112.plan.table+
      4*24212*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*291590947217 := by decide +kernel
private theorem range65From23491To4161 : Segment 65 23491 24212 4018 4161 :=
  paid (pc:=62) (v:=291590947217) (by decide) source112_valid tests65_112_4018 fee65_112_24212 (by decide +kernel)

private theorem range65From23491 : Win 65 23491 24212 :=
  complete (by decide) (by decide) (join_population (join_population range65From23491To3590 range65From23491To3639) (join_population range65From23491To4018 range65From23491To4161))

private theorem fee65_116_24892 :
    PopulationFees20258.bill (n:=24892) (PopulationFees20258.tabulate (24892-1) 256) source116.plan.table+
      4*24892*NaturalPopulation20258.weights source116.extras≤source116.plan.scale*241846558696 := by decide +kernel
private theorem range65From24213To3595 : Segment 65 24213 24892 0 3595 :=
  paid (pc:=69) (v:=241846558696) (by decide) source116_valid tests65_116_0 fee65_116_24892 (by decide +kernel)

private theorem tests65_116_3595 : ∀ z∈source116.plan.table,z.1.Valid 65 3595 := by decide +kernel
private theorem range65From24213To3639 : Segment 65 24213 24892 3595 3639 :=
  paid (pc:=69) (v:=241846558696) (by decide) source116_valid tests65_116_3595 fee65_116_24892 (by decide +kernel)

private theorem fee65_108_24892 :
    PopulationFees20258.bill (n:=24892) (PopulationFees20258.tabulate (24892-1) 256) source108.plan.table+
      4*24892*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*293267159956 := by decide +kernel
private theorem range65From24213To3945 : Segment 65 24213 24892 3639 3945 :=
  paid (pc:=67) (v:=293267159956) (by decide) source108_valid tests65_108_3639 fee65_108_24892 (by decide +kernel)

private theorem tests65_112_3945 : ∀ z∈source112.plan.table,z.1.Valid 65 3945 := by decide +kernel
private theorem fee65_112_24892 :
    PopulationFees20258.bill (n:=24892) (PopulationFees20258.tabulate (24892-1) 256) source112.plan.table+
      4*24892*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*306703176857 := by decide +kernel
private theorem range65From24213To4161 : Segment 65 24213 24892 3945 4161 :=
  paid (pc:=63) (v:=306703176857) (by decide) source112_valid tests65_112_3945 fee65_112_24892 (by decide +kernel)

private theorem range65From24213 : Win 65 24213 24892 :=
  complete (by decide) (by decide) (join_population (join_population range65From24213To3595 range65From24213To3639) (join_population range65From24213To3945 range65From24213To4161))

private theorem tests65_115_0 : ∀ z∈source115.plan.table,z.1.Valid 65 0 := by decide +kernel
private theorem fee65_115_25560 :
    PopulationFees20258.bill (n:=25560) (PopulationFees20258.tabulate (25560-1) 256) source115.plan.table+
      4*25560*NaturalPopulation20258.weights source115.extras≤source115.plan.scale*253720956511 := by decide +kernel
private theorem range65From24893To3601 : Segment 65 24893 25560 0 3601 :=
  paid (pc:=70) (v:=253720956511) (by decide) source115_valid tests65_115_0 fee65_115_25560 (by decide +kernel)

private theorem tests65_115_3601 : ∀ z∈source115.plan.table,z.1.Valid 65 3601 := by decide +kernel
private theorem range65From24893To3640 : Segment 65 24893 25560 3601 3640 :=
  paid (pc:=70) (v:=253720956511) (by decide) source115_valid tests65_115_3601 fee65_115_25560 (by decide +kernel)

private theorem tests65_108_3640 : ∀ z∈source108.plan.table,z.1.Valid 65 3640 := by decide +kernel
private theorem fee65_108_25560 :
    PopulationFees20258.bill (n:=25560) (PopulationFees20258.tabulate (25560-1) 256) source108.plan.table+
      4*25560*NaturalPopulation20258.weights source108.extras≤source108.plan.scale*307997765476 := by decide +kernel
private theorem range65From24893To3896 : Segment 65 24893 25560 3640 3896 :=
  paid (pc:=68) (v:=307997765476) (by decide) source108_valid tests65_108_3640 fee65_108_25560 (by decide +kernel)

private theorem tests65_112_3896 : ∀ z∈source112.plan.table,z.1.Valid 65 3896 := by decide +kernel
private theorem fee65_112_25560 :
    PopulationFees20258.bill (n:=25560) (PopulationFees20258.tabulate (25560-1) 256) source112.plan.table+
      4*25560*NaturalPopulation20258.weights source112.extras≤source112.plan.scale*321901185737 := by decide +kernel
private theorem range65From24893To4161 : Segment 65 24893 25560 3896 4161 :=
  paid (pc:=65) (v:=321901185737) (by decide) source112_valid tests65_112_3896 fee65_112_25560 (by decide +kernel)

private theorem range65From24893 : Win 65 24893 25560 :=
  complete (by decide) (by decide) (join_population (join_population range65From24893To3601 range65From24893To3640) (join_population range65From24893To3896 range65From24893To4161))

theorem cut65From20258 : Win 65 20258 25560 :=
  (join_ground (join_ground range65From20258 (join_ground range65From21697 range65From22681)) (join_ground range65From23491 (join_ground range65From24213 range65From24893)))

end JSP233.FiniteCutRanges20258
