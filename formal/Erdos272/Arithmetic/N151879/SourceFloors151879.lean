module

public import Erdos272.Arithmetic.N151879.SourceCoverChecks151879G00
public import Erdos272.Arithmetic.N151879.SourceCoverChecks151879G01
public import Erdos272.Arithmetic.N151879.SourceCoverChecks151879G02
public import Erdos272.Arithmetic.N153080.SourceFloors153080

@[expose] public section

namespace JSP233.SourceFloors151879
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join012_00 : ∀ s, 1170 ≤ s → s < 1690 → 52316 ≤ physicalK s 12 :=
  append_cover SourceCoverChecks151879G00.bound0012 SourceCoverChecks151879G00.bound0013
#print axioms join012_00

theorem floor067 : Floor 117 76 127310 := by
  have suffix : Floor 119 76 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor054
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks151879G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 117 74 121496 := by
  have suffix : Floor 120 74 121496 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor121
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks151879G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 117 71 113020 := by
  have suffix : Floor 122 71 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor120
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks151879G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 117 68 105190 := by
  have suffix : Floor 119 68 105190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor052
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks151879G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 117 64 94956 := by
  have suffix : Floor 119 64 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor051
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks151879G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 163 58 127310 := by
  have suffix : Floor 166 58 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor050
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks151879G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 117 58 81654 := by
  have suffix : Floor 119 58 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor049
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks151879G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 163 56 121496 := by
  have suffix : Floor 168 56 121496 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor109
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks151879G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 163 54 113020 := by
  have suffix : Floor 170 54 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor108
  intro s hs hbig
  by_cases h : s < 170
  · exact SourceCoverChecks151879G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 117 54 72618 := by
  have suffix : Floor 124 54 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor106
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks151879G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 163 52 105190 := by
  have suffix : Floor 166 52 105190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor047
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks151879G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 163 49 94956 := by
  have suffix : Floor 164 49 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor399
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks151879G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 117 49 62162 := by
  have suffix : Floor 118 49 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor049
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks151879G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 234 45 127310 := by
  have suffix : Floor 244 45 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor097
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks151879G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 163 45 81654 := by
  have suffix : Floor 166 45 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor044
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks151879G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 234 44 121496 := by
  have suffix : Floor 240 44 121496 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor093
  intro s hs hbig
  by_cases h : s < 240
  · exact SourceCoverChecks151879G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 117 44 52316 := by
  have suffix : Floor 127 44 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor083
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks151879G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 234 43 113020 := by
  have suffix : Floor 238 43 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor042
  intro s hs hbig
  by_cases h : s < 238
  · exact SourceCoverChecks151879G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 163 42 72618 := by
  have suffix : Floor 173 42 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor090
  intro s hs hbig
  by_cases h : s < 173
  · exact SourceCoverChecks151879G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 234 39 94956 := by
  have suffix : Floor 238 39 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor040
  intro s hs hbig
  by_cases h : s < 238
  · exact SourceCoverChecks151879G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 163 39 62162 := by
  have suffix : Floor 165 39 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor041
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks151879G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 351 36 127310 := by
  have suffix : Floor 357 36 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor038
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks151879G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 234 36 81654 := by
  have suffix : Floor 238 36 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor037
  intro s hs hbig
  by_cases h : s < 238
  · exact SourceCoverChecks151879G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 351 35 121496 := by
  have suffix : Floor 360 35 121496 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor281
  intro s hs hbig
  by_cases h : s < 360
  · exact SourceCoverChecks151879G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 163 35 52316 := by
  have suffix : Floor 165 35 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor037
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks151879G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 351 34 113020 := by
  have suffix : Floor 357 34 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor034
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks151879G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 234 34 72618 := by
  have suffix : Floor 248 34 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor074
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks151879G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 117 34 33624 := by
  have suffix : Floor 129 34 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor066
  intro s hs hbig
  by_cases h : s < 129
  · exact SourceCoverChecks151879G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 351 33 105190 := by
  have suffix : Floor 354 33 105190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor035
  intro s hs hbig
  by_cases h : s < 354
  · exact SourceCoverChecks151879G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 351 31 94956 := by
  have suffix : Floor 357 31 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor031
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks151879G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 234 31 62162 := by
  have suffix : Floor 236 31 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor033
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks151879G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 351 29 81654 := by
  have suffix : Floor 357 29 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor030
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks151879G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 234 28 52316 := by
  have suffix : Floor 236 28 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor208
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks151879G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 163 28 33624 := by
  have suffix : Floor 165 28 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor029
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks151879G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 585 27 127310 := by
  have suffix : Floor 610 27 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor061
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks151879G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 351 27 72618 := by
  have suffix : Floor 372 27 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor056
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks151879G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 585 26 113020 := by
  have suffix : Floor 590 26 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor028
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks151879G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 655 25 121496 := by
  have suffix : Floor 658 25 121496 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor054
  intro s hs hbig
  by_cases h : s < 658
  · exact SourceCoverChecks151879G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 585 25 105190 := by
  have suffix : Floor 590 25 105190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor027
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks151879G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 351 25 62162 := by
  have suffix : Floor 354 25 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor026
  intro s hs hbig
  by_cases h : s < 354
  · exact SourceCoverChecks151879G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 610 24 105190 := by
  have suffix : Floor 612 24 105190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor051
  intro s hs hbig
  by_cases h : s < 612
  · exact SourceCoverChecks151879G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 581 24 94956 := by
  have suffix : Floor 587 24 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor024
  intro s hs hbig
  by_cases h : s < 587
  · exact SourceCoverChecks151879G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 539 23 81654 := by
  have suffix : Floor 545 23 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor023
  intro s hs hbig
  by_cases h : s < 545
  · exact SourceCoverChecks151879G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 234 23 33624 := by
  have suffix : Floor 236 23 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor023
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks151879G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 509 22 72618 := by
  have suffix : Floor 514 22 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor043
  intro s hs hbig
  by_cases h : s < 514
  · exact SourceCoverChecks151879G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 472 21 62162 := by
  have suffix : Floor 476 21 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor022
  intro s hs hbig
  by_cases h : s < 476
  · exact SourceCoverChecks151879G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 434 21 52316 := by
  have suffix : Floor 438 21 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor021
  intro s hs hbig
  by_cases h : s < 438
  · exact SourceCoverChecks151879G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 117 21 14055 := by
  have suffix : Floor 118 21 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor020
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks151879G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 350 18 33624 := by
  have suffix : Floor 353 18 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor019
  intro s hs hbig
  by_cases h : s < 353
  · exact SourceCoverChecks151879G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 163 18 14055 := by
  have suffix : Floor 165 18 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor018
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks151879G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 1170 17 94956 := by
  have suffix : Floor 1190 17 94956 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor016
  intro s hs hbig
  by_cases h : s < 1190
  · exact SourceCoverChecks151879G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 1170 15 81654 := by
  have suffix : Floor 1530 15 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor023
  intro s hs hbig
  by_cases h : s < 1530
  · exact SourceCoverChecks151879G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 224 15 14055 := by
  have suffix : Floor 225 15 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor015
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks151879G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 1170 14 62162 := by
  have suffix : Floor 1180 14 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor014
  intro s hs hbig
  by_cases h : s < 1180
  · exact SourceCoverChecks151879G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 585 14 33624 := by
  have suffix : Floor 590 14 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor013
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks151879G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 1170 12 52316 := by
  have suffix : Floor 1690 12 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor028
  intro s hs hbig
  by_cases h : s < 1690
  · exact join012_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 351 12 14055 := by
  have suffix : Floor 354 12 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor011
  intro s hs hbig
  by_cases h : s < 354
  · exact SourceCoverChecks151879G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 3744 11 127310 := by
  have suffix : Floor 3776 11 127310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor010
  intro s hs hbig
  by_cases h : s < 3776
  · exact SourceCoverChecks151879G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 117 11 3732 := by
  have suffix : Floor 118 11 3732 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor009
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks151879G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 3744 10 113020 := by
  have suffix : Floor 3904 10 113020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor016
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks151879G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 1170 10 33624 := by
  have suffix : Floor 1180 10 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor007
  intro s hs hbig
  by_cases h : s < 1180
  · exact SourceCoverChecks151879G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 3744 9 81654 := by
  have suffix : Floor 3808 9 81654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor006
  intro s hs hbig
  by_cases h : s < 3808
  · exact SourceCoverChecks151879G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 585 9 14055 := by
  have suffix : Floor 590 9 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor005
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks151879G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 3744 8 72618 := by
  have suffix : Floor 3968 8 72618 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor008
  intro s hs hbig
  by_cases h : s < 3968
  · exact SourceCoverChecks151879G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 3744 7 52316 := by
  have suffix : Floor 3776 7 52316 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor003
  intro s hs hbig
  by_cases h : s < 3776
  · exact SourceCoverChecks151879G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 1170 7 14055 := by
  have suffix : Floor 1180 7 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor002
  intro s hs hbig
  by_cases h : s < 1180
  · exact SourceCoverChecks151879G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 3744 6 33624 := by
  have suffix : Floor 3776 6 33624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor001
  intro s hs hbig
  by_cases h : s < 3776
  · exact SourceCoverChecks151879G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 3744 4 14055 := by
  have suffix : Floor 3776 4 14055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor000
  intro s hs hbig
  by_cases h : s < 3776
  · exact SourceCoverChecks151879G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors151879
