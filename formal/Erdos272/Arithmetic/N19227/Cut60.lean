module

public import Erdos272.Arithmetic.N20258.Sources.Source100
public import Erdos272.Arithmetic.N20258.Sources.Source104
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.Credit19227
open PopulationRanges20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem fee83At19608 :
    PopulationFees20258.bill (n:=19608) (PopulationFees20258.tabulate (19608-1) 256) PopulationSources20258.source104.plan.table+
      4*19608*NaturalPopulation20258.weights PopulationSources20258.source104.extras≤PopulationSources20258.source104.plan.scale*140050313293 := by decide +kernel
private theorem from19227To2863 : Segment 60 19227 19608 0 2863 :=
  paid (pc:=70) (v:=140050313293) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At19608 (by decide +kernel)

private theorem from19227To2902 : Segment 60 19227 19608 2863 2902 :=
  paid (pc:=70) (v:=140050313293) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At19608 (by decide +kernel)

private theorem from19227To2904 : Segment 60 19227 19608 2902 2904 :=
  paid (pc:=70) (v:=140050313293) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At19608 (by decide +kernel)

private theorem fee80At19608 :
    PopulationFees20258.bill (n:=19608) (PopulationFees20258.tabulate (19608-1) 256) PopulationSources20258.source100.plan.table+
      4*19608*NaturalPopulation20258.weights PopulationSources20258.source100.extras≤PopulationSources20258.source100.plan.scale*227140471435 := by decide +kernel
private theorem from19227To3486 : Segment 60 19227 19608 2904 3486 :=
  paid (pc:=64) (v:=227140471435) (by decide) PopulationSources20258.source100_valid (by decide +kernel) fee80At19608 (by decide +kernel)

private theorem fee132At19608 :
    PopulationFees20258.bill (n:=19608) (PopulationFees20258.tabulate (19608-1) 256) PopulationSources20258.source105.plan.table+
      4*19608*NaturalPopulation20258.weights PopulationSources20258.source105.extras≤PopulationSources20258.source105.plan.scale*231724202551 := by decide +kernel
private theorem from19227To3541 : Segment 60 19227 19608 3486 3541 :=
  paid (pc:=61) (v:=231724202551) (by decide) PopulationSources20258.source105_valid (by decide +kernel) fee132At19608 (by decide +kernel)

private theorem range19227 : Win 60 19227 19608 :=
  complete (by decide) (by decide) (join_population (join_population from19227To2863 from19227To2902) (join_population from19227To2904 (join_population from19227To3486 from19227To3541)))

private theorem fee83At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source104.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source104.extras≤PopulationSources20258.source104.plan.scale*141001727933 := by decide +kernel
private theorem from19609To3030 : Segment 60 19609 19682 0 3030 :=
  paid (pc:=71) (v:=141001727933) (by decide) PopulationSources20258.source104_valid (by decide +kernel) fee83At19682 (by decide +kernel)

private theorem fee84At19682 :
    PopulationFees20258.bill (n:=19682) (PopulationFees20258.tabulate (19682-1) 256) PopulationSources20258.source106.plan.table+
      4*19682*NaturalPopulation20258.weights PopulationSources20258.source106.extras≤PopulationSources20258.source106.plan.scale*237993727066 := by decide +kernel
private theorem from19609To3541 : Segment 60 19609 19682 3030 3541 :=
  paid (pc:=63) (v:=237993727066) (by decide) PopulationSources20258.source106_valid (by decide +kernel) fee84At19682 (by decide +kernel)

private theorem range19609 : Win 60 19609 19682 :=
  complete (by decide) (by decide) (join_population from19609To3030 from19609To3541)

theorem cut60 : Win 60 19227 19682 :=
  (join_ground range19227 range19609)

end JSP233.Credit19227
