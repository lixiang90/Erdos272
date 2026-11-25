module

public import Erdos272.Arithmetic.N158375.SourceCoverChecks158375G00
public import Erdos272.Arithmetic.N158375.SourceCoverChecks158375G01
public import Erdos272.Arithmetic.N158375.SourceCoverChecks158375G02
public import Erdos272.Arithmetic.N158375.SourceCoverChecks158375G03
public import Erdos272.Arithmetic.N158375.SourceCoverChecks158375G04
public import Erdos272.Arithmetic.N180000.SourceFloors180000

@[expose] public section

namespace JSP233.SourceFloors158375
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join000_00 : ∀ s, 3840 ≤ s → s < 4768 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0000 SourceCoverChecks158375G00.bound0001
#print axioms join000_00

theorem join000_01 : ∀ s, 4768 ≤ s → s < 5792 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0002 SourceCoverChecks158375G00.bound0003
#print axioms join000_01

theorem join000_02 : ∀ s, 5792 ≤ s → s < 6816 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0004 SourceCoverChecks158375G00.bound0005
#print axioms join000_02

theorem join000_03 : ∀ s, 6816 ≤ s → s < 7878 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0006 SourceCoverChecks158375G00.bound0007
#print axioms join000_03

theorem join000_04 : ∀ s, 7878 ≤ s → s < 9213 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0008 SourceCoverChecks158375G00.bound0009
#print axioms join000_04

theorem join000_05 : ∀ s, 9213 ≤ s → s < 10396 → 14845 ≤ physicalK s 4 :=
  append_cover SourceCoverChecks158375G00.bound0010 SourceCoverChecks158375G00.bound0011
#print axioms join000_05

theorem join000_06 : ∀ s, 3840 ≤ s → s < 5792 → 14845 ≤ physicalK s 4 :=
  append_cover join000_00 join000_01
#print axioms join000_06

theorem join000_07 : ∀ s, 5792 ≤ s → s < 7878 → 14845 ≤ physicalK s 4 :=
  append_cover join000_02 join000_03
#print axioms join000_07

theorem join000_08 : ∀ s, 7878 ≤ s → s < 10396 → 14845 ≤ physicalK s 4 :=
  append_cover join000_04 join000_05
#print axioms join000_08

theorem join000_09 : ∀ s, 3840 ≤ s → s < 7878 → 14845 ≤ physicalK s 4 :=
  append_cover join000_06 join000_07
#print axioms join000_09

theorem join000_10 : ∀ s, 3840 ≤ s → s < 10396 → 14845 ≤ physicalK s 4 :=
  append_cover join000_09 join000_08
#print axioms join000_10

theorem join003_00 : ∀ s, 3968 ≤ s → s < 4800 → 38234 ≤ physicalK s 6 :=
  append_cover SourceCoverChecks158375G00.bound0014 SourceCoverChecks158375G00.bound0015
#print axioms join003_00

theorem join004_00 : ∀ s, 1200 ≤ s → s < 2542 → 14845 ≤ physicalK s 7 :=
  append_cover SourceCoverChecks158375G00.bound0016 SourceCoverChecks158375G00.bound0017
#print axioms join004_00

theorem join004_01 : ∀ s, 2542 ≤ s → s < 3719 → 14845 ≤ physicalK s 7 :=
  append_cover SourceCoverChecks158375G00.bound0018 SourceCoverChecks158375G00.bound0019
#print axioms join004_01

theorem join004_02 : ∀ s, 1200 ≤ s → s < 3719 → 14845 ≤ physicalK s 7 :=
  append_cover join004_00 join004_01
#print axioms join004_02

theorem join008_00 : ∀ s, 3968 ≤ s → s < 4780 → 74052 ≤ physicalK s 8 :=
  append_cover SourceCoverChecks158375G00.bound0023 SourceCoverChecks158375G00.bound0024
#print axioms join008_00

theorem join008_01 : ∀ s, 3968 ≤ s → s < 4800 → 74052 ≤ physicalK s 8 :=
  append_cover join008_00 SourceCoverChecks158375G00.bound0025
#print axioms join008_01

theorem floor126 : Floor 124 79 145554 := by
  have suffix : Floor 130 79 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor094
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks158375G04.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 122 79 143244 := by
  have suffix : Floor 124 79 143244 :=
    weaken (by decide) (by decide) floor126
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks158375G04.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 120 77 134264 := by
  have suffix : Floor 127 77 134264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor106
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G04.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 122 75 131094 := by
  have suffix : Floor 127 75 131094 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor106
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G04.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 124 73 127634 := by
  have suffix : Floor 130 73 127634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor092
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks158375G04.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 120 73 122562 := by
  have suffix : Floor 124 73 122562 :=
    weaken (by decide) (by decide) floor122
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks158375G04.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 122 69 113724 := by
  have suffix : Floor 127 69 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor104
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G04.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 120 69 111224 := by
  have suffix : Floor 122 69 111224 :=
    weaken (by decide) (by decide) floor120
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks158375G04.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 124 65 105724 := by
  have suffix : Floor 130 65 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor090
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks158375G04.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 120 65 100808 := by
  have suffix : Floor 124 65 100808 :=
    weaken (by decide) (by decide) floor118
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks158375G04.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 170 61 143244 := by
  have suffix : Floor 177 61 143244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor102
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G04.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 122 61 93546 := by
  have suffix : Floor 127 61 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor099
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G04.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 173 60 145554 := by
  have suffix : Floor 179 60 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor101
  intro s hs hbig
  by_cases h : s < 179
  · exact SourceCoverChecks158375G04.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 168 59 134264 := by
  have suffix : Floor 177 59 134264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor097
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G04.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 120 59 86818 := by
  have suffix : Floor 130 59 86818 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor084
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks158375G04.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 170 57 131094 := by
  have suffix : Floor 177 57 131094 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor097
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G04.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 173 56 127634 := by
  have suffix : Floor 177 56 127634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor097
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G03.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 168 56 122562 := by
  have suffix : Floor 173 56 122562 :=
    weaken (by decide) (by decide) floor110
  intro s hs hbig
  by_cases h : s < 173
  · exact SourceCoverChecks158375G03.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 170 53 113724 := by
  have suffix : Floor 177 53 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor095
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G03.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 168 53 111224 := by
  have suffix : Floor 170 53 111224 :=
    weaken (by decide) (by decide) floor108
  intro s hs hbig
  by_cases h : s < 170
  · exact SourceCoverChecks158375G03.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 124 52 74052 := by
  have suffix : Floor 150 52 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor118
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks158375G03.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 122 51 70277 := by
  have suffix : Floor 127 51 70277 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor093
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G03.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 120 51 66916 := by
  have suffix : Floor 122 51 66916 :=
    weaken (by decide) (by decide) floor105
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks158375G03.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 173 50 105724 := by
  have suffix : Floor 175 50 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor407
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks158375G03.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 168 50 100808 := by
  have suffix : Floor 169 50 100808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor406
  intro s hs hbig
  by_cases h : s < 169
  · exact SourceCoverChecks158375G03.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 248 47 145554 := by
  have suffix : Floor 260 47 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor076
  intro s hs hbig
  by_cases h : s < 260
  · exact SourceCoverChecks158375G03.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 244 47 143244 := by
  have suffix : Floor 248 47 143244 :=
    weaken (by decide) (by decide) floor101
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks158375G03.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 170 47 93546 := by
  have suffix : Floor 177 47 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor089
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G03.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 240 46 134264 := by
  have suffix : Floor 254 46 134264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor086
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G03.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 244 45 131094 := by
  have suffix : Floor 254 45 131094 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor086
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G03.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 168 45 86818 := by
  have suffix : Floor 182 45 86818 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor073
  intro s hs hbig
  by_cases h : s < 182
  · exact SourceCoverChecks158375G03.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 120 45 55588 := by
  have suffix : Floor 127 45 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor083
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks158375G03.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 248 44 127634 := by
  have suffix : Floor 256 44 127634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor085
  intro s hs hbig
  by_cases h : s < 256
  · exact SourceCoverChecks158375G03.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 240 44 122562 := by
  have suffix : Floor 248 44 122562 :=
    weaken (by decide) (by decide) floor094
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks158375G03.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 244 42 113724 := by
  have suffix : Floor 254 42 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor081
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G03.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 240 42 111224 := by
  have suffix : Floor 244 42 111224 :=
    weaken (by decide) (by decide) floor092
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks158375G03.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 173 41 74052 := by
  have suffix : Floor 189 41 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor329
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks158375G03.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 248 40 105724 := by
  have suffix : Floor 260 40 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor068
  intro s hs hbig
  by_cases h : s < 260
  · exact SourceCoverChecks158375G03.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 170 40 70277 := by
  have suffix : Floor 177 40 70277 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor079
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G03.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 168 39 66916 := by
  have suffix : Floor 180 39 66916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor312
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks158375G03.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 372 37 145554 := by
  have suffix : Floor 378 37 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor301
  intro s hs hbig
  by_cases h : s < 378
  · exact SourceCoverChecks158375G03.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 366 37 143244 := by
  have suffix : Floor 372 37 143244 :=
    weaken (by decide) (by decide) floor086
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks158375G03.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 360 37 134264 := by
  have suffix : Floor 366 37 134264 :=
    weaken (by decide) (by decide) floor085
  intro s hs hbig
  by_cases h : s < 366
  · exact SourceCoverChecks158375G03.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 244 37 93546 := by
  have suffix : Floor 254 37 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor075
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G03.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 240 37 86818 := by
  have suffix : Floor 244 37 86818 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks158375G03.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 366 36 131094 := by
  have suffix : Floor 381 36 131094 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor073
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks158375G03.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 168 36 55588 := by
  have suffix : Floor 177 36 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor071
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks158375G03.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 124 36 38234 := by
  have suffix : Floor 150 36 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor084
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks158375G03.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 122 35 36927 := by
  have suffix : Floor 148 35 36927 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor020
  intro s hs hbig
  by_cases h : s < 148
  · exact SourceCoverChecks158375G02.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 120 35 35610 := by
  have suffix : Floor 122 35 35610 :=
    weaken (by decide) (by decide) floor078
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks158375G02.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 366 33 113724 := by
  have suffix : Floor 381 33 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor069
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks158375G02.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 360 33 111224 := by
  have suffix : Floor 366 33 111224 :=
    weaken (by decide) (by decide) floor076
  intro s hs hbig
  by_cases h : s < 366
  · exact SourceCoverChecks158375G02.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 248 33 74052 := by
  have suffix : Floor 264 33 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor255
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks158375G02.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 372 32 105724 := by
  have suffix : Floor 390 32 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor056
  intro s hs hbig
  by_cases h : s < 390
  · exact SourceCoverChecks158375G02.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 244 32 70277 := by
  have suffix : Floor 254 32 70277 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor067
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G02.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 240 32 66916 := by
  have suffix : Floor 244 32 66916 :=
    weaken (by decide) (by decide) floor072
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks158375G02.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 360 31 100808 := by
  have suffix : Floor 411 31 100808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor073
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks158375G02.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 366 30 93546 := by
  have suffix : Floor 381 30 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor062
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks158375G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 620 29 145554 := by
  have suffix : Floor 621 29 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor222
  intro s hs hbig
  by_cases h : s < 621
  · exact SourceCoverChecks158375G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 360 29 86818 := by
  have suffix : Floor 390 29 86818 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor049
  intro s hs hbig
  by_cases h : s < 390
  · exact SourceCoverChecks158375G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 240 29 55588 := by
  have suffix : Floor 254 29 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor058
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 173 29 38234 := by
  have suffix : Floor 210 29 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor063
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks158375G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 610 28 143244 := by
  have suffix : Floor 650 28 143244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor046
  intro s hs hbig
  by_cases h : s < 650
  · exact SourceCoverChecks158375G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 170 28 36927 := by
  have suffix : Floor 207 28 36927 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor016
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks158375G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 168 28 35610 := by
  have suffix : Floor 170 28 35610 :=
    weaken (by decide) (by decide) floor063
  intro s hs hbig
  by_cases h : s < 170
  · exact SourceCoverChecks158375G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 610 27 131094 := by
  have suffix : Floor 635 27 131094 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor056
  intro s hs hbig
  by_cases h : s < 635
  · exact SourceCoverChecks158375G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 600 27 122562 := by
  have suffix : Floor 610 27 122562 :=
    weaken (by decide) (by decide) floor061
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks158375G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 716 26 145554 := by
  have suffix : Floor 765 26 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor062
  intro s hs hbig
  by_cases h : s < 765
  · exact SourceCoverChecks158375G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 710 26 143244 := by
  have suffix : Floor 716 26 143244 :=
    weaken (by decide) (by decide) floor059
  intro s hs hbig
  by_cases h : s < 716
  · exact SourceCoverChecks158375G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 688 26 134264 := by
  have suffix : Floor 710 26 134264 :=
    weaken (by decide) (by decide) floor058
  intro s hs hbig
  by_cases h : s < 710
  · exact SourceCoverChecks158375G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 372 26 74052 := by
  have suffix : Floor 432 26 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor182
  intro s hs hbig
  by_cases h : s < 432
  · exact SourceCoverChecks158375G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 366 26 70277 := by
  have suffix : Floor 372 26 70277 :=
    weaken (by decide) (by decide) floor056
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks158375G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 658 25 122562 := by
  have suffix : Floor 670 25 122562 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor058
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks158375G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 610 25 113724 := by
  have suffix : Floor 635 25 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor049
  intro s hs hbig
  by_cases h : s < 635
  · exact SourceCoverChecks158375G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 600 25 111224 := by
  have suffix : Floor 610 25 111224 :=
    weaken (by decide) (by decide) floor053
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks158375G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 612 24 105724 := by
  have suffix : Floor 650 24 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor040
  intro s hs hbig
  by_cases h : s < 650
  · exact SourceCoverChecks158375G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 598 24 100808 := by
  have suffix : Floor 612 24 100808 :=
    weaken (by decide) (by decide) floor051
  intro s hs hbig
  by_cases h : s < 612
  · exact SourceCoverChecks158375G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 576 24 93546 := by
  have suffix : Floor 598 24 93546 :=
    weaken (by decide) (by decide) floor050
  intro s hs hbig
  by_cases h : s < 598
  · exact SourceCoverChecks158375G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 555 23 86818 := by
  have suffix : Floor 635 23 86818 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor047
  intro s hs hbig
  by_cases h : s < 635
  · exact SourceCoverChecks158375G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 360 23 55588 := by
  have suffix : Floor 381 23 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor045
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks158375G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 248 23 38234 := by
  have suffix : Floor 300 23 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor048
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks158375G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 244 23 36927 := by
  have suffix : Floor 248 23 36927 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks158375G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 240 23 35610 := by
  have suffix : Floor 244 23 35610 :=
    weaken (by decide) (by decide) floor045
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks158375G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 514 22 74052 := by
  have suffix : Floor 567 22 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor138
  intro s hs hbig
  by_cases h : s < 567
  · exact SourceCoverChecks158375G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 501 22 70277 := by
  have suffix : Floor 514 22 70277 :=
    weaken (by decide) (by decide) floor043
  intro s hs hbig
  by_cases h : s < 514
  · exact SourceCoverChecks158375G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 489 22 66916 := by
  have suffix : Floor 501 22 66916 :=
    weaken (by decide) (by decide) floor042
  intro s hs hbig
  by_cases h : s < 501
  · exact SourceCoverChecks158375G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 447 21 55588 := by
  have suffix : Floor 540 21 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor128
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks158375G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 120 21 14845 := by
  have suffix : Floor 254 21 14845 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor042
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks158375G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 372 19 38234 := by
  have suffix : Floor 450 19 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor031
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks158375G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 366 19 36927 := by
  have suffix : Floor 372 19 36927 :=
    weaken (by decide) (by decide) floor038
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks158375G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 360 19 35610 := by
  have suffix : Floor 366 19 35610 :=
    weaken (by decide) (by decide) floor037
  intro s hs hbig
  by_cases h : s < 366
  · exact SourceCoverChecks158375G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 168 18 14845 := by
  have suffix : Floor 381 18 14845 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor030
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks158375G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 1240 17 105724 := by
  have suffix : Floor 1300 17 105724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor024
  intro s hs hbig
  by_cases h : s < 1300
  · exact SourceCoverChecks158375G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 1220 16 93546 := by
  have suffix : Floor 1270 16 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor028
  intro s hs hbig
  by_cases h : s < 1270
  · exact SourceCoverChecks158375G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 1200 16 86818 := by
  have suffix : Floor 1220 16 86818 :=
    weaken (by decide) (by decide) floor033
  intro s hs hbig
  by_cases h : s < 1220
  · exact SourceCoverChecks158375G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 620 15 38234 := by
  have suffix : Floor 750 15 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor020
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks158375G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 230 15 14845 := by
  have suffix : Floor 620 15 14845 :=
    weaken (by decide) (by decide) floor031
  intro s hs hbig
  by_cases h : s < 620
  · exact SourceCoverChecks158375G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 1240 14 74052 := by
  have suffix : Floor 1500 14 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor022
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks158375G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 1220 14 70277 := by
  have suffix : Floor 1240 14 70277 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 1240
  · exact SourceCoverChecks158375G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 1200 14 66916 := by
  have suffix : Floor 1220 14 66916 :=
    weaken (by decide) (by decide) floor028
  intro s hs hbig
  by_cases h : s < 1220
  · exact SourceCoverChecks158375G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 610 14 36927 := by
  have suffix : Floor 740 14 36927 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor005
  intro s hs hbig
  by_cases h : s < 740
  · exact SourceCoverChecks158375G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 600 14 35610 := by
  have suffix : Floor 610 14 35610 :=
    weaken (by decide) (by decide) floor026
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks158375G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 1200 13 55588 := by
  have suffix : Floor 1270 13 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor023
  intro s hs hbig
  by_cases h : s < 1270
  · exact SourceCoverChecks158375G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 360 12 14845 := by
  have suffix : Floor 1270 12 14845 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor012
  intro s hs hbig
  by_cases h : s < 1270
  · exact SourceCoverChecks158375G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 3968 11 145554 := by
  have suffix : Floor 4160 11 145554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor012
  intro s hs hbig
  by_cases h : s < 4160
  · exact SourceCoverChecks158375G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 3904 11 143244 := by
  have suffix : Floor 3968 11 143244 :=
    weaken (by decide) (by decide) floor022
  intro s hs hbig
  by_cases h : s < 3968
  · exact SourceCoverChecks158375G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 3840 11 134264 := by
  have suffix : Floor 3904 11 134264 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks158375G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 124 11 4234 :=
  of_prefix_tail (C := 461) (by decide) (by decide) (by decide +kernel) SourceCoverChecks158375G01.bound0036
#print axioms floor019

theorem floor018 : Floor 122 11 4085 := by
  have suffix : Floor 124 11 4085 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks158375G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 120 11 3950 := by
  have suffix : Floor 122 11 3950 :=
    weaken (by decide) (by decide) floor018
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks158375G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 3904 10 113724 := by
  have suffix : Floor 4064 10 113724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor015
  intro s hs hbig
  by_cases h : s < 4064
  · exact SourceCoverChecks158375G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 3840 10 111224 := by
  have suffix : Floor 3904 10 111224 :=
    weaken (by decide) (by decide) floor016
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks158375G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 1240 10 38234 := by
  have suffix : Floor 1500 10 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor007
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks158375G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 1220 10 36927 := by
  have suffix : Floor 1240 10 36927 :=
    weaken (by decide) (by decide) floor014
  intro s hs hbig
  by_cases h : s < 1240
  · exact SourceCoverChecks158375G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 1200 10 35610 := by
  have suffix : Floor 1220 10 35610 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 1220
  · exact SourceCoverChecks158375G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 600 10 14845 := by
  have suffix : Floor 1200 10 14845 :=
    weaken (by decide) (by decide) floor012
  intro s hs hbig
  by_cases h : s < 1200
  · exact SourceCoverChecks158375G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 3904 9 93546 := by
  have suffix : Floor 4064 9 93546 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor007
  intro s hs hbig
  by_cases h : s < 4064
  · exact SourceCoverChecks158375G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 3840 9 86818 := by
  have suffix : Floor 3904 9 86818 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks158375G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 3968 8 74052 := by
  have suffix : Floor 4800 8 74052 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor002
  intro s hs hbig
  by_cases h : s < 4800
  · exact join008_01 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 3904 8 70277 := by
  have suffix : Floor 3968 8 70277 :=
    weaken (by decide) (by decide) floor008
  intro s hs hbig
  by_cases h : s < 3968
  · exact SourceCoverChecks158375G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 3840 8 66916 := by
  have suffix : Floor 3904 8 66916 :=
    weaken (by decide) (by decide) floor007
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks158375G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 3840 7 55588 := by
  have suffix : Floor 4064 7 55588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor003
  intro s hs hbig
  by_cases h : s < 4064
  · exact SourceCoverChecks158375G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 1200 7 14845 :=
  of_prefix_tail (C := 3719) (by decide) (by decide) (by decide +kernel) join004_02
#print axioms floor004

theorem floor003 : Floor 3968 6 38234 := by
  have suffix : Floor 4800 6 38234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor000
  intro s hs hbig
  by_cases h : s < 4800
  · exact join003_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 3904 6 36927 := by
  have suffix : Floor 3968 6 36927 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 3968
  · exact SourceCoverChecks158375G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 3840 6 35610 := by
  have suffix : Floor 3904 6 35610 :=
    weaken (by decide) (by decide) floor002
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks158375G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 3840 4 14845 :=
  of_prefix_tail (C := 10396) (by decide) (by decide) (by decide +kernel) join000_10
#print axioms floor000

end JSP233.SourceFloors158375
