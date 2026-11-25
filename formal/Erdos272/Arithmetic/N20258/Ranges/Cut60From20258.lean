module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source100
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
private theorem fee60_104_20628 :
    PopulationFees20258.bill (n:=20628) (PopulationFees20258.tabulate (20628-1) 256) source104.plan.table+
      4*20628*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*153517581478 := by decide +kernel
private theorem range60From20258To2872 : Segment 60 20258 20628 0 2872 :=
  paid (pc:=72) (v:=153517581478) (by decide) source104_valid tests60_104_0 fee60_104_20628 (by decide +kernel)

private theorem tests60_104_2872 : ∀ z∈source104.plan.table,z.1.Valid 60 2872 := by decide +kernel
private theorem range60From20258To2903 : Segment 60 20258 20628 2872 2903 :=
  paid (pc:=72) (v:=153517581478) (by decide) source104_valid tests60_104_2872 fee60_104_20628 (by decide +kernel)

private theorem tests60_104_2903 : ∀ z∈source104.plan.table,z.1.Valid 60 2903 := by decide +kernel
private theorem range60From20258To2905 : Segment 60 20258 20628 2903 2905 :=
  paid (pc:=72) (v:=153517581478) (by decide) source104_valid tests60_104_2903 fee60_104_20628 (by decide +kernel)

private theorem tests60_100_2905 : ∀ z∈source100.plan.table,z.1.Valid 60 2905 := by decide +kernel
private theorem fee60_100_20628 :
    PopulationFees20258.bill (n:=20628) (PopulationFees20258.tabulate (20628-1) 256) source100.plan.table+
      4*20628*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*248607244886 := by decide +kernel
private theorem range60From20258To3215 : Segment 60 20258 20628 2905 3215 :=
  paid (pc:=69) (v:=248607244886) (by decide) source100_valid tests60_100_2905 fee60_100_20628 (by decide +kernel)

private theorem tests60_105_3215 : ∀ z∈source105.plan.table,z.1.Valid 60 3215 := by decide +kernel
private theorem fee60_105_20628 :
    PopulationFees20258.bill (n:=20628) (PopulationFees20258.tabulate (20628-1) 256) source105.plan.table+
      4*20628*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*253577058750 := by decide +kernel
private theorem range60From20258To3541 : Segment 60 20258 20628 3215 3541 :=
  paid (pc:=64) (v:=253577058750) (by decide) source105_valid tests60_105_3215 fee60_105_20628 (by decide +kernel)

private theorem range60From20258 : Win 60 20258 20628 :=
  complete (by decide) (by decide) (join_population (join_population range60From20258To2872 range60From20258To2903) (join_population range60From20258To2905 (join_population range60From20258To3215 range60From20258To3541)))

private theorem fee60_104_21012 :
    PopulationFees20258.bill (n:=21012) (PopulationFees20258.tabulate (21012-1) 256) source104.plan.table+
      4*21012*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*158775500694 := by decide +kernel
private theorem range60From20629To2872 : Segment 60 20629 21012 0 2872 :=
  paid (pc:=72) (v:=158775500694) (by decide) source104_valid tests60_104_0 fee60_104_21012 (by decide +kernel)

private theorem range60From20629To2902 : Segment 60 20629 21012 2872 2902 :=
  paid (pc:=72) (v:=158775500694) (by decide) source104_valid tests60_104_2872 fee60_104_21012 (by decide +kernel)

private theorem tests60_104_2902 : ∀ z∈source104.plan.table,z.1.Valid 60 2902 := by decide +kernel
private theorem range60From20629To2904 : Segment 60 20629 21012 2902 2904 :=
  paid (pc:=72) (v:=158775500694) (by decide) source104_valid tests60_104_2902 fee60_104_21012 (by decide +kernel)

private theorem tests60_100_2904 : ∀ z∈source100.plan.table,z.1.Valid 60 2904 := by decide +kernel
private theorem fee60_100_21012 :
    PopulationFees20258.bill (n:=21012) (PopulationFees20258.tabulate (21012-1) 256) source100.plan.table+
      4*21012*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*257124450596 := by decide +kernel
private theorem range60From20629To3161 : Segment 60 20629 21012 2904 3161 :=
  paid (pc:=70) (v:=257124450596) (by decide) source100_valid tests60_100_2904 fee60_100_21012 (by decide +kernel)

private theorem tests60_105_3161 : ∀ z∈source105.plan.table,z.1.Valid 60 3161 := by decide +kernel
private theorem fee60_105_21012 :
    PopulationFees20258.bill (n:=21012) (PopulationFees20258.tabulate (21012-1) 256) source105.plan.table+
      4*21012*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*262094872226 := by decide +kernel
private theorem range60From20629To3541 : Segment 60 20629 21012 3161 3541 :=
  paid (pc:=65) (v:=262094872226) (by decide) source105_valid tests60_105_3161 fee60_105_21012 (by decide +kernel)

private theorem range60From20629 : Win 60 20629 21012 :=
  complete (by decide) (by decide) (join_population (join_population range60From20629To2872 range60From20629To2902) (join_population range60From20629To2904 (join_population range60From20629To3161 range60From20629To3541)))

private theorem fee60_104_21412 :
    PopulationFees20258.bill (n:=21412) (PopulationFees20258.tabulate (21412-1) 256) source104.plan.table+
      4*21412*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*164385302286 := by decide +kernel
private theorem range60From21013To2875 : Segment 60 21013 21412 0 2875 :=
  paid (pc:=73) (v:=164385302286) (by decide) source104_valid tests60_104_0 fee60_104_21412 (by decide +kernel)

private theorem tests60_104_2875 : ∀ z∈source104.plan.table,z.1.Valid 60 2875 := by decide +kernel
private theorem range60From21013To2902 : Segment 60 21013 21412 2875 2902 :=
  paid (pc:=73) (v:=164385302286) (by decide) source104_valid tests60_104_2875 fee60_104_21412 (by decide +kernel)

private theorem range60From21013To2904 : Segment 60 21013 21412 2902 2904 :=
  paid (pc:=73) (v:=164385302286) (by decide) source104_valid tests60_104_2902 fee60_104_21412 (by decide +kernel)

private theorem fee60_100_21412 :
    PopulationFees20258.bill (n:=21412) (PopulationFees20258.tabulate (21412-1) 256) source100.plan.table+
      4*21412*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*265854967318 := by decide +kernel
private theorem range60From21013To3124 : Segment 60 21013 21412 2904 3124 :=
  paid (pc:=71) (v:=265854967318) (by decide) source100_valid tests60_100_2904 fee60_100_21412 (by decide +kernel)

private theorem tests60_105_3124 : ∀ z∈source105.plan.table,z.1.Valid 60 3124 := by decide +kernel
private theorem fee60_105_21412 :
    PopulationFees20258.bill (n:=21412) (PopulationFees20258.tabulate (21412-1) 256) source105.plan.table+
      4*21412*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*271174123668 := by decide +kernel
private theorem range60From21013To3541 : Segment 60 21013 21412 3124 3541 :=
  paid (pc:=65) (v:=271174123668) (by decide) source105_valid tests60_105_3124 fee60_105_21412 (by decide +kernel)

private theorem range60From21013 : Win 60 21013 21412 :=
  complete (by decide) (by decide) (join_population (join_population range60From21013To2875 range60From21013To2902) (join_population range60From21013To2904 (join_population range60From21013To3124 range60From21013To3541)))

private theorem fee60_104_21840 :
    PopulationFees20258.bill (n:=21840) (PopulationFees20258.tabulate (21840-1) 256) source104.plan.table+
      4*21840*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*170340964979 := by decide +kernel
private theorem range60From21413To2877 : Segment 60 21413 21840 0 2877 :=
  paid (pc:=73) (v:=170340964979) (by decide) source104_valid tests60_104_0 fee60_104_21840 (by decide +kernel)

private theorem tests60_104_2877 : ∀ z∈source104.plan.table,z.1.Valid 60 2877 := by decide +kernel
private theorem range60From21413To2904 : Segment 60 21413 21840 2877 2904 :=
  paid (pc:=73) (v:=170340964979) (by decide) source104_valid tests60_104_2877 fee60_104_21840 (by decide +kernel)

private theorem fee60_100_21840 :
    PopulationFees20258.bill (n:=21840) (PopulationFees20258.tabulate (21840-1) 256) source100.plan.table+
      4*21840*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*275463240599 := by decide +kernel
private theorem range60From21413To3090 : Segment 60 21413 21840 2904 3090 :=
  paid (pc:=71) (v:=275463240599) (by decide) source100_valid tests60_100_2904 fee60_100_21840 (by decide +kernel)

private theorem tests60_105_3090 : ∀ z∈source105.plan.table,z.1.Valid 60 3090 := by decide +kernel
private theorem fee60_105_21840 :
    PopulationFees20258.bill (n:=21840) (PopulationFees20258.tabulate (21840-1) 256) source105.plan.table+
      4*21840*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*280856990660 := by decide +kernel
private theorem range60From21413To3541 : Segment 60 21413 21840 3090 3541 :=
  paid (pc:=66) (v:=280856990660) (by decide) source105_valid tests60_105_3090 fee60_105_21840 (by decide +kernel)

private theorem range60From21413 : Win 60 21413 21840 :=
  complete (by decide) (by decide) (join_population (join_population range60From21413To2877 range60From21413To2904) (join_population range60From21413To3090 range60From21413To3541))

private theorem fee60_104_22305 :
    PopulationFees20258.bill (n:=22305) (PopulationFees20258.tabulate (22305-1) 256) source104.plan.table+
      4*22305*NaturalPopulation20258.weights source104.extras≤source104.plan.scale*177060508013 := by decide +kernel
private theorem range60From21841To2878 : Segment 60 21841 22305 0 2878 :=
  paid (pc:=73) (v:=177060508013) (by decide) source104_valid tests60_104_0 fee60_104_22305 (by decide +kernel)

private theorem tests60_104_2878 : ∀ z∈source104.plan.table,z.1.Valid 60 2878 := by decide +kernel
private theorem range60From21841To2902 : Segment 60 21841 22305 2878 2902 :=
  paid (pc:=73) (v:=177060508013) (by decide) source104_valid tests60_104_2878 fee60_104_22305 (by decide +kernel)

private theorem range60From21841To2904 : Segment 60 21841 22305 2902 2904 :=
  paid (pc:=73) (v:=177060508013) (by decide) source104_valid tests60_104_2902 fee60_104_22305 (by decide +kernel)

private theorem fee60_100_22305 :
    PopulationFees20258.bill (n:=22305) (PopulationFees20258.tabulate (22305-1) 256) source100.plan.table+
      4*22305*NaturalPopulation20258.weights source100.extras≤source100.plan.scale*286210181992 := by decide +kernel
private theorem range60From21841To3057 : Segment 60 21841 22305 2904 3057 :=
  paid (pc:=72) (v:=286210181992) (by decide) source100_valid tests60_100_2904 fee60_100_22305 (by decide +kernel)

private theorem tests60_106_3057 : ∀ z∈source106.plan.table,z.1.Valid 60 3057 := by decide +kernel
private theorem fee60_106_22305 :
    PopulationFees20258.bill (n:=22305) (PopulationFees20258.tabulate (22305-1) 256) source106.plan.table+
      4*22305*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*297589251230 := by decide +kernel
private theorem range60From21841To3541 : Segment 60 21841 22305 3057 3541 :=
  paid (pc:=67) (v:=297589251230) (by decide) source106_valid tests60_106_3057 fee60_106_22305 (by decide +kernel)

private theorem range60From21841 : Win 60 21841 22305 :=
  complete (by decide) (by decide) (join_population (join_population range60From21841To2878 range60From21841To2902) (join_population range60From21841To2904 (join_population range60From21841To3057 range60From21841To3541)))

theorem cut60From20258 : Win 60 20258 22305 :=
  (join_ground (join_ground range60From20258 range60From20629) (join_ground range60From21013 (join_ground range60From21413 range60From21841)))

end JSP233.FiniteCutRanges20258
