module

public import Erdos272.Arithmetic.N243614.SourceCoverChecks243614G00
public import Erdos272.Arithmetic.N243614.SourceCoverChecks243614G01
public import Erdos272.Arithmetic.N250262.SourceFloors250262

@[expose] public section

namespace JSP233.SourceFloors243614
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join005_00 : ∀ s, 740 ≤ s → s < 1480 → 38180 ≤ physicalK s 13 :=
  append_cover SourceCoverChecks243614G00.bound0005 SourceCoverChecks243614G00.bound0006
#print axioms join005_00

theorem floor034 : Floor 148 89 225160 := by
  have suffix : Floor 158 89 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor168
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks243614G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 148 77 177276 := by
  have suffix : Floor 156 77 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor161
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks243614G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 207 68 225160 := by
  have suffix : Floor 216 68 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor508
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks243614G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 207 59 177276 := by
  have suffix : Floor 214 59 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor145
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks243614G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 148 57 110740 := by
  have suffix : Floor 180 57 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor426
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks243614G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 296 53 225160 := by
  have suffix : Floor 316 53 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor133
  intro s hs hbig
  by_cases h : s < 316
  · exact SourceCoverChecks243614G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 296 47 177276 := by
  have suffix : Floor 312 47 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor126
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks243614G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 207 45 110740 := by
  have suffix : Floor 252 45 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor355
  intro s hs hbig
  by_cases h : s < 252
  · exact SourceCoverChecks243614G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 148 45 73682 := by
  have suffix : Floor 189 45 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor329
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks243614G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 444 43 225160 := by
  have suffix : Floor 450 43 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor111
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks243614G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 444 38 177276 := by
  have suffix : Floor 450 38 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor103
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks243614G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 296 37 110740 := by
  have suffix : Floor 360 37 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor281
  intro s hs hbig
  by_cases h : s < 360
  · exact SourceCoverChecks243614G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 207 36 73682 := by
  have suffix : Floor 207 36 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor292
  exact suffix
#print axioms floor022

theorem floor021 : Floor 740 32 225160 := by
  have suffix : Floor 790 32 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor083
  intro s hs hbig
  by_cases h : s < 790
  · exact SourceCoverChecks243614G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 148 31 38180 := by
  have suffix : Floor 210 31 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor063
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks243614G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 296 30 73682 := by
  have suffix : Floor 296 30 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor231
  exact suffix
#print axioms floor019

theorem floor018 : Floor 740 29 177276 := by
  have suffix : Floor 750 29 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor068
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks243614G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 444 29 110740 := by
  have suffix : Floor 540 29 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor211
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks243614G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 207 26 38180 := by
  have suffix : Floor 300 26 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor048
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks243614G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 444 24 73682 := by
  have suffix : Floor 567 24 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor138
  intro s hs hbig
  by_cases h : s < 567
  · exact SourceCoverChecks243614G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 1480 23 225160 := by
  have suffix : Floor 1500 23 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor053
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks243614G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 740 23 110740 := by
  have suffix : Floor 750 23 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor050
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks243614G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 296 21 38180 := by
  have suffix : Floor 450 21 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor031
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks243614G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 1480 20 177276 := by
  have suffix : Floor 1640 20 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor122
  intro s hs hbig
  by_cases h : s < 1640
  · exact SourceCoverChecks243614G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 740 18 73682 := by
  have suffix : Floor 945 18 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor095
  intro s hs hbig
  by_cases h : s < 945
  · exact SourceCoverChecks243614G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 444 17 38180 := by
  have suffix : Floor 750 17 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor020
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks243614G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 1480 16 110740 := by
  have suffix : Floor 1530 16 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor027
  intro s hs hbig
  by_cases h : s < 1530
  · exact SourceCoverChecks243614G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 4736 13 225160 := by
  have suffix : Floor 4800 13 225160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor016
  intro s hs hbig
  by_cases h : s < 4800
  · exact SourceCoverChecks243614G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 1480 13 73682 := by
  have suffix : Floor 1890 13 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor039
  intro s hs hbig
  by_cases h : s < 1890
  · exact SourceCoverChecks243614G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 740 13 38180 := by
  have suffix : Floor 1480 13 38180 :=
    weaken (by decide) (by decide) floor006
  intro s hs hbig
  by_cases h : s < 1480
  · exact join005_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 4736 12 177276 := by
  have suffix : Floor 4800 12 177276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor015
  intro s hs hbig
  by_cases h : s < 4800
  · exact SourceCoverChecks243614G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 1480 10 38180 := by
  have suffix : Floor 1500 10 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor007
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks243614G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 4736 9 110740 := by
  have suffix : Floor 4896 9 110740 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor006
  intro s hs hbig
  by_cases h : s < 4896
  · exact SourceCoverChecks243614G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 4736 8 73682 := by
  have suffix : Floor 4800 8 73682 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor002
  intro s hs hbig
  by_cases h : s < 4800
  · exact SourceCoverChecks243614G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 4736 6 38180 := by
  have suffix : Floor 4800 6 38180 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor000
  intro s hs hbig
  by_cases h : s < 4800
  · exact SourceCoverChecks243614G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors243614
