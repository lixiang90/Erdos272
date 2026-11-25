module

public import Erdos272.Arithmetic.N130000.SourceCoverChecks130000G00
public import Erdos272.Arithmetic.N130000.SourceCoverChecks130000G01
public import Erdos272.Arithmetic.N130000.SourceCoverChecks130000G02
public import Erdos272.Arithmetic.N142758.SourceFloors142758

@[expose] public section

namespace JSP233.SourceFloors130000
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join003_00 : ∀ s, 3456 ≤ s → s < 4361 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0003 SourceCoverChecks130000G00.bound0004
#print axioms join003_00

theorem join003_01 : ∀ s, 4361 ≤ s → s < 5385 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0005 SourceCoverChecks130000G00.bound0006
#print axioms join003_01

theorem join003_02 : ∀ s, 5385 ≤ s → s < 6489 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0007 SourceCoverChecks130000G00.bound0008
#print axioms join003_02

theorem join003_03 : ∀ s, 6489 ≤ s → s < 7984 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0009 SourceCoverChecks130000G00.bound0010
#print axioms join003_03

theorem join003_04 : ∀ s, 7984 ≤ s → s < 9520 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0011 SourceCoverChecks130000G00.bound0012
#print axioms join003_04

theorem join003_05 : ∀ s, 9520 ≤ s → s < 10351 → 22168 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks130000G00.bound0013 SourceCoverChecks130000G00.bound0014
#print axioms join003_05

theorem join003_06 : ∀ s, 3456 ≤ s → s < 5385 → 22168 ≤ physicalK s 5 :=
  append_cover join003_00 join003_01
#print axioms join003_06

theorem join003_07 : ∀ s, 5385 ≤ s → s < 7984 → 22168 ≤ physicalK s 5 :=
  append_cover join003_02 join003_03
#print axioms join003_07

theorem join003_08 : ∀ s, 7984 ≤ s → s < 10351 → 22168 ≤ physicalK s 5 :=
  append_cover join003_04 join003_05
#print axioms join003_08

theorem join003_09 : ∀ s, 3456 ≤ s → s < 7984 → 22168 ≤ physicalK s 5 :=
  append_cover join003_06 join003_07
#print axioms join003_09

theorem join003_10 : ∀ s, 3456 ≤ s → s < 10351 → 22168 ≤ physicalK s 5 :=
  append_cover join003_09 join003_08
#print axioms join003_10

theorem join005_00 : ∀ s, 3584 ≤ s → s < 4130 → 40604 ≤ physicalK s 6 :=
  append_cover SourceCoverChecks130000G00.bound0016 SourceCoverChecks130000G00.bound0017
#print axioms join005_00

theorem join005_01 : ∀ s, 4130 ≤ s → s < 4800 → 40604 ≤ physicalK s 6 :=
  append_cover SourceCoverChecks130000G00.bound0018 SourceCoverChecks130000G00.bound0019
#print axioms join005_01

theorem join005_02 : ∀ s, 3584 ≤ s → s < 4800 → 40604 ≤ physicalK s 6 :=
  append_cover join005_00 join005_01
#print axioms join005_02

theorem join010_00 : ∀ s, 4160 ≤ s → s < 4772 → 81729 ≤ physicalK s 8 :=
  append_cover SourceCoverChecks130000G00.bound0024 SourceCoverChecks130000G00.bound0025
#print axioms join010_00

theorem join010_01 : ∀ s, 4160 ≤ s → s < 4896 → 81729 ≤ physicalK s 8 :=
  append_cover join010_00 SourceCoverChecks130000G00.bound0026
#print axioms join010_01

theorem join017_00 : ∀ s, 4160 ≤ s → s < 4480 → 102352 ≤ physicalK s 9 :=
  append_cover SourceCoverChecks130000G00.bound0033 SourceCoverChecks130000G00.bound0034
#print axioms join017_00

theorem floor164 : Floor 112 75 117706 := by
  have suffix : Floor 114 75 117706 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor196
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0181 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor164

theorem floor163 : Floor 108 74 108530 := by
  have suffix : Floor 114 74 108530 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor194
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0180 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor163

theorem floor162 : Floor 110 73 109906 := by
  have suffix : Floor 114 73 109906 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor194
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0179 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor162

theorem floor161 : Floor 108 73 106610 := by
  have suffix : Floor 110 73 106610 :=
    weaken (by decide) (by decide) floor162
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0178 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor161

theorem floor160 : Floor 112 71 107258 := by
  have suffix : Floor 114 71 107258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor192
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0177 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor160

theorem floor159 : Floor 110 71 104206 := by
  have suffix : Floor 112 71 104206 :=
    weaken (by decide) (by decide) floor160
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G02.bound0176 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor159

theorem floor158 : Floor 108 71 102402 := by
  have suffix : Floor 110 71 102402 :=
    weaken (by decide) (by decide) floor159
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0175 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor158

theorem floor157 : Floor 108 70 98798 := by
  have suffix : Floor 114 70 98798 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor190
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0174 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor157

theorem floor156 : Floor 130 69 123984 := by
  have suffix : Floor 134 69 123984 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor133
  intro s hs hbig
  by_cases h : s < 134
  · exact SourceCoverChecks130000G02.bound0173 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor156

theorem floor155 : Floor 110 69 99850 := by
  have suffix : Floor 114 69 99850 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor190
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0172 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor155

theorem floor154 : Floor 108 69 96962 := by
  have suffix : Floor 110 69 96962 :=
    weaken (by decide) (by decide) floor155
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0171 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor154

theorem floor153 : Floor 108 68 94586 := by
  have suffix : Floor 114 68 94586 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor188
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0170 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor153

theorem floor152 : Floor 112 67 96512 := by
  have suffix : Floor 114 67 96512 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor188
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0169 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor152

theorem floor151 : Floor 110 67 94792 := by
  have suffix : Floor 112 67 94792 :=
    weaken (by decide) (by decide) floor152
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G02.bound0168 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor151

theorem floor150 : Floor 108 67 92738 := by
  have suffix : Floor 110 67 92738 :=
    weaken (by decide) (by decide) floor151
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0167 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor150

theorem floor149 : Floor 108 65 87896 := by
  have suffix : Floor 114 65 87896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor186
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0166 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor149

theorem floor148 : Floor 112 63 87386 := by
  have suffix : Floor 114 63 87386 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor183
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0165 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor148

theorem floor147 : Floor 110 63 85330 := by
  have suffix : Floor 112 63 85330 :=
    weaken (by decide) (by decide) floor148
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G02.bound0164 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor147

theorem floor146 : Floor 108 63 82916 := by
  have suffix : Floor 110 63 82916 :=
    weaken (by decide) (by decide) floor147
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0163 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor146

theorem floor145 : Floor 130 61 102352 := by
  have suffix : Floor 140 61 102352 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor125
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks130000G02.bound0162 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 108 61 78882 := by
  have suffix : Floor 114 61 78882 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor181
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0161 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 110 59 76384 := by
  have suffix : Floor 114 59 76384 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor176
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0160 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 108 59 74654 := by
  have suffix : Floor 110 59 74654 :=
    weaken (by decide) (by decide) floor143
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0159 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 108 57 70436 := by
  have suffix : Floor 114 57 70436 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor176
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0158 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 112 55 70568 := by
  have suffix : Floor 115 55 70568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor171
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks130000G02.bound0157 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 110 55 68488 := by
  have suffix : Floor 112 55 68488 :=
    weaken (by decide) (by decide) floor140
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G02.bound0156 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 108 55 66720 := by
  have suffix : Floor 110 55 66720 :=
    weaken (by decide) (by decide) floor139
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0155 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 165 53 109906 := by
  have suffix : Floor 168 53 109906 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor107
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks130000G02.bound0154 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 162 53 108530 := by
  have suffix : Floor 165 53 108530 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor050
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks130000G02.bound0153 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 130 53 81729 := by
  have suffix : Floor 153 53 81729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor119
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks130000G02.bound0152 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 108 53 63044 := by
  have suffix : Floor 114 53 63044 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor167
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0151 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 168 51 107258 := by
  have suffix : Floor 175 51 107258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor407
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks130000G02.bound0150 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 162 51 102402 := by
  have suffix : Floor 168 51 102402 :=
    weaken (by decide) (by decide) floor133
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks130000G02.bound0149 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 110 51 61300 := by
  have suffix : Floor 115 51 61300 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor162
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks130000G02.bound0148 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 108 51 59676 := by
  have suffix : Floor 110 51 59676 :=
    weaken (by decide) (by decide) floor131
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0147 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 195 50 123984 := by
  have suffix : Floor 218 50 123984 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor124
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks130000G02.bound0146 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 165 50 99850 := by
  have suffix : Floor 168 50 99850 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor102
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks130000G02.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 162 50 98798 := by
  have suffix : Floor 165 50 98798 :=
    weaken (by decide) (by decide) floor128
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks130000G02.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 108 49 56080 := by
  have suffix : Floor 114 49 56080 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor158
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 112 47 55310 := by
  have suffix : Floor 120 47 55310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor095
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks130000G02.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 108 47 52416 := by
  have suffix : Floor 112 47 52416 :=
    weaken (by decide) (by decide) floor125
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G02.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 108 46 49583 := by
  have suffix : Floor 114 46 49583 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor153
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 195 45 102352 := by
  have suffix : Floor 203 45 102352 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor063
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks130000G02.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 108 44 46946 := by
  have suffix : Floor 117 44 46946 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor051
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks130000G02.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 189 42 87896 := by
  have suffix : Floor 225 42 87896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor330
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks130000G02.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 110 42 44327 := by
  have suffix : Floor 114 42 44327 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor140
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G02.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 108 42 42392 := by
  have suffix : Floor 110 42 42392 :=
    weaken (by decide) (by decide) floor119
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G02.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 196 41 87386 := by
  have suffix : Floor 225 41 87386 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor330
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks130000G02.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 189 41 82916 := by
  have suffix : Floor 196 41 82916 :=
    weaken (by decide) (by decide) floor117
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks130000G02.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 195 40 81729 := by
  have suffix : Floor 214 40 81729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor096
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks130000G02.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 112 40 40604 := by
  have suffix : Floor 150 40 40604 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor084
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks130000G02.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 192 39 76384 := by
  have suffix : Floor 210 39 76384 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor095
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks130000G02.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 189 39 74654 := by
  have suffix : Floor 192 39 74654 :=
    weaken (by decide) (by decide) floor113
  intro s hs hbig
  by_cases h : s < 192
  · exact SourceCoverChecks130000G02.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 108 39 37189 := by
  have suffix : Floor 124 39 37189 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor079
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks130000G02.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 189 38 70436 := by
  have suffix : Floor 207 38 70436 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor022
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks130000G01.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 196 37 70568 := by
  have suffix : Floor 207 37 70568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor022
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks130000G01.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 192 37 68488 := by
  have suffix : Floor 196 37 68488 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor089
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks130000G01.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 189 36 63044 := by
  have suffix : Floor 191 36 63044 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor086
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks130000G01.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 336 35 117706 := by
  have suffix : Floor 342 35 117706 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor128
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks130000G01.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 330 35 109906 := by
  have suffix : Floor 336 35 109906 :=
    weaken (by decide) (by decide) floor106
  intro s hs hbig
  by_cases h : s < 336
  · exact SourceCoverChecks130000G01.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 324 35 108530 := by
  have suffix : Floor 330 35 108530 :=
    weaken (by decide) (by decide) floor105
  intro s hs hbig
  by_cases h : s < 330
  · exact SourceCoverChecks130000G01.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 192 35 61300 := by
  have suffix : Floor 228 35 61300 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor126
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 130 35 40181 := by
  have suffix : Floor 150 35 40181 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor084
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks130000G01.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 108 35 30453 := by
  have suffix : Floor 114 35 30453 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor119
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G01.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 336 34 107258 := by
  have suffix : Floor 342 34 107258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor123
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks130000G01.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 189 34 59676 := by
  have suffix : Floor 228 34 59676 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor117
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 390 33 123984 := by
  have suffix : Floor 402 33 123984 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor081
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks130000G01.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 330 33 99850 := by
  have suffix : Floor 334 33 99850 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor257
  intro s hs hbig
  by_cases h : s < 334
  · exact SourceCoverChecks130000G01.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 324 33 98798 := by
  have suffix : Floor 330 33 98798 :=
    weaken (by decide) (by decide) floor097
  intro s hs hbig
  by_cases h : s < 330
  · exact SourceCoverChecks130000G01.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 189 33 56080 := by
  have suffix : Floor 228 33 56080 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor117
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 110 33 29814 := by
  have suffix : Floor 127 33 29814 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor064
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks130000G01.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 336 32 96512 := by
  have suffix : Floor 342 32 96512 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor116
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks130000G01.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 189 32 52416 := by
  have suffix : Floor 228 32 52416 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor109
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 224 30 55310 := by
  have suffix : Floor 228 30 55310 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor109
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 220 29 52249 := by
  have suffix : Floor 228 29 52249 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor106
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 216 29 49583 := by
  have suffix : Floor 220 29 49583 :=
    weaken (by decide) (by decide) floor090
  intro s hs hbig
  by_cases h : s < 220
  · exact SourceCoverChecks130000G01.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 108 29 22168 := by
  have suffix : Floor 159 29 22168 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor102
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks130000G01.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 216 28 46946 := by
  have suffix : Floor 225 28 46946 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor206
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks130000G01.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 195 28 40181 := by
  have suffix : Floor 210 28 40181 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor063
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks130000G01.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 390 27 81729 := by
  have suffix : Floor 432 27 81729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor182
  intro s hs hbig
  by_cases h : s < 432
  · exact SourceCoverChecks130000G01.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 220 27 44327 := by
  have suffix : Floor 228 27 44327 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor095
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 224 26 40604 := by
  have suffix : Floor 300 26 40604 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor048
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks130000G01.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 658 25 123984 := by
  have suffix : Floor 670 25 123984 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor058
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks130000G01.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 641 25 117706 := by
  have suffix : Floor 645 25 117706 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor050
  intro s hs hbig
  by_cases h : s < 645
  · exact SourceCoverChecks130000G01.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 216 25 37189 := by
  have suffix : Floor 248 25 37189 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor046
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks130000G01.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 604 24 104206 := by
  have suffix : Floor 610 24 104206 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor027
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks130000G01.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 599 24 102402 := by
  have suffix : Floor 603 24 102402 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor085
  intro s hs hbig
  by_cases h : s < 603
  · exact SourceCoverChecks130000G01.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 591 24 99850 := by
  have suffix : Floor 598 24 99850 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor050
  intro s hs hbig
  by_cases h : s < 598
  · exact SourceCoverChecks130000G01.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 588 24 98798 := by
  have suffix : Floor 591 24 98798 :=
    weaken (by decide) (by decide) floor077
  intro s hs hbig
  by_cases h : s < 591
  · exact SourceCoverChecks130000G01.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 540 24 87896 := by
  have suffix : Floor 559 24 87896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor079
  intro s hs hbig
  by_cases h : s < 559
  · exact SourceCoverChecks130000G01.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 555 23 87896 := by
  have suffix : Floor 559 23 87896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor079
  intro s hs hbig
  by_cases h : s < 559
  · exact SourceCoverChecks130000G01.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 554 23 87386 := by
  have suffix : Floor 555 23 87386 :=
    weaken (by decide) (by decide) floor074
  intro s hs hbig
  by_cases h : s < 555
  · exact SourceCoverChecks130000G01.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 547 23 85330 := by
  have suffix : Floor 552 23 85330 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor005
  intro s hs hbig
  by_cases h : s < 552
  · exact SourceCoverChecks130000G01.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 540 23 82916 := by
  have suffix : Floor 545 23 82916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor023
  intro s hs hbig
  by_cases h : s < 545
  · exact SourceCoverChecks130000G01.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 536 23 81729 := by
  have suffix : Floor 540 23 81729 :=
    weaken (by decide) (by decide) floor071
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks130000G01.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 527 23 78882 := by
  have suffix : Floor 535 23 78882 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor024
  intro s hs hbig
  by_cases h : s < 535
  · exact SourceCoverChecks130000G01.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 519 23 76384 := by
  have suffix : Floor 522 23 76384 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor075
  intro s hs hbig
  by_cases h : s < 522
  · exact SourceCoverChecks130000G01.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 216 23 30453 := by
  have suffix : Floor 228 23 30453 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor068
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 513 22 74654 := by
  have suffix : Floor 567 22 74654 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor138
  intro s hs hbig
  by_cases h : s < 567
  · exact SourceCoverChecks130000G01.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 499 22 70568 := by
  have suffix : Floor 504 22 70568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor072
  intro s hs hbig
  by_cases h : s < 504
  · exact SourceCoverChecks130000G01.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 498 22 70436 := by
  have suffix : Floor 499 22 70436 :=
    weaken (by decide) (by decide) floor065
  intro s hs hbig
  by_cases h : s < 499
  · exact SourceCoverChecks130000G01.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 492 22 68488 := by
  have suffix : Floor 496 22 68488 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor003
  intro s hs hbig
  by_cases h : s < 496
  · exact SourceCoverChecks130000G01.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 485 22 66720 := by
  have suffix : Floor 489 22 66720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor041
  intro s hs hbig
  by_cases h : s < 489
  · exact SourceCoverChecks130000G01.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 220 22 29814 := by
  have suffix : Floor 228 22 29814 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor068
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G01.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 472 21 63044 := by
  have suffix : Floor 476 21 63044 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor022
  intro s hs hbig
  by_cases h : s < 476
  · exact SourceCoverChecks130000G01.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 466 21 61300 := by
  have suffix : Floor 472 21 61300 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor022
  intro s hs hbig
  by_cases h : s < 472
  · exact SourceCoverChecks130000G01.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 460 21 59676 := by
  have suffix : Floor 466 21 59676 :=
    weaken (by decide) (by decide) floor059
  intro s hs hbig
  by_cases h : s < 466
  · exact SourceCoverChecks130000G01.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 446 21 56080 := by
  have suffix : Floor 454 21 56080 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor066
  intro s hs hbig
  by_cases h : s < 454
  · exact SourceCoverChecks130000G01.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 443 21 55310 := by
  have suffix : Floor 446 21 55310 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 446
  · exact SourceCoverChecks130000G01.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 432 21 52416 := by
  have suffix : Floor 434 21 52416 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor064
  intro s hs hbig
  by_cases h : s < 434
  · exact SourceCoverChecks130000G01.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 112 21 13055 := by
  have suffix : Floor 114 21 13055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor061
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G01.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 110 21 12589 := by
  have suffix : Floor 112 21 12589 :=
    weaken (by decide) (by decide) floor054
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks130000G01.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 108 21 12048 := by
  have suffix : Floor 110 21 12048 :=
    weaken (by decide) (by decide) floor053
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G01.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 431 20 52249 := by
  have suffix : Floor 507 20 52249 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor112
  intro s hs hbig
  by_cases h : s < 507
  · exact SourceCoverChecks130000G01.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 420 20 49583 := by
  have suffix : Floor 431 20 49583 :=
    weaken (by decide) (by decide) floor051
  intro s hs hbig
  by_cases h : s < 431
  · exact SourceCoverChecks130000G01.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 409 20 46946 := by
  have suffix : Floor 420 20 46946 :=
    weaken (by decide) (by decide) floor050
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks130000G01.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 398 20 44327 := by
  have suffix : Floor 402 20 44327 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor059
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks130000G01.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 389 19 42392 := by
  have suffix : Floor 450 19 42392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor031
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks130000G01.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 381 19 40604 := by
  have suffix : Floor 389 19 40604 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 389
  · exact SourceCoverChecks130000G00.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 379 19 40181 := by
  have suffix : Floor 381 19 40181 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks130000G00.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 365 19 37189 := by
  have suffix : Floor 372 19 37189 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor038
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks130000G00.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 216 19 22168 := by
  have suffix : Floor 340 19 22168 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor056
  intro s hs hbig
  by_cases h : s < 340
  · exact SourceCoverChecks130000G00.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 331 18 30453 := by
  have suffix : Floor 340 18 30453 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor056
  intro s hs hbig
  by_cases h : s < 340
  · exact SourceCoverChecks130000G00.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 328 18 29814 := by
  have suffix : Floor 331 18 29814 :=
    weaken (by decide) (by decide) floor042
  intro s hs hbig
  by_cases h : s < 331
  · exact SourceCoverChecks130000G00.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 1120 17 87386 := by
  have suffix : Floor 1140 17 87386 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor052
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks130000G00.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 285 17 22168 := by
  have suffix : Floor 381 17 22168 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor030
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks130000G00.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 1100 16 85330 := by
  have suffix : Floor 1140 16 85330 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor052
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks130000G00.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 1080 16 82916 := by
  have suffix : Floor 1100 16 82916 :=
    weaken (by decide) (by decide) floor038
  intro s hs hbig
  by_cases h : s < 1100
  · exact SourceCoverChecks130000G00.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 1120 15 70568 := by
  have suffix : Floor 1140 15 70568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor050
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks130000G00.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 1080 15 70436 := by
  have suffix : Floor 1120 15 70436 :=
    weaken (by decide) (by decide) floor036
  intro s hs hbig
  by_cases h : s < 1120
  · exact SourceCoverChecks130000G00.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 214 15 13055 := by
  have suffix : Floor 218 15 13055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor047
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks130000G00.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 211 15 12589 := by
  have suffix : Floor 214 15 12589 :=
    weaken (by decide) (by decide) floor034
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks130000G00.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 1080 14 63044 := by
  have suffix : Floor 1140 14 63044 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor044
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks130000G00.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 206 14 12048 := by
  have suffix : Floor 342 14 12048 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor035
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks130000G00.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 1080 13 52416 := by
  have suffix : Floor 1140 13 52416 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor040
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks130000G00.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 3584 11 117706 := by
  have suffix : Floor 3648 11 117706 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor032
  intro s hs hbig
  by_cases h : s < 3648
  · exact SourceCoverChecks130000G00.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 3520 11 109906 := by
  have suffix : Floor 3584 11 109906 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 3456 11 108530 := by
  have suffix : Floor 3520 11 108530 :=
    weaken (by decide) (by decide) floor028
  intro s hs hbig
  by_cases h : s < 3520
  · exact SourceCoverChecks130000G00.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 1300 11 40181 := by
  have suffix : Floor 1500 11 40181 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor007
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks130000G00.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 130 11 4732 := by
  have suffix : Floor 228 11 4732 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor023
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks130000G00.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 112 11 3489 := by
  have suffix : Floor 114 11 3489 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor028
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks130000G00.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 4160 10 123984 := by
  have suffix : Floor 4288 10 123984 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor015
  intro s hs hbig
  by_cases h : s < 4288
  · exact SourceCoverChecks130000G00.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 3584 10 107258 := by
  have suffix : Floor 3648 10 107258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor027
  intro s hs hbig
  by_cases h : s < 3648
  · exact SourceCoverChecks130000G00.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 3520 10 104206 := by
  have suffix : Floor 3584 10 104206 :=
    weaken (by decide) (by decide) floor022
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 3456 10 102402 := by
  have suffix : Floor 3520 10 102402 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 3520
  · exact SourceCoverChecks130000G00.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 110 10 3352 := by
  have suffix : Floor 127 10 3352 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor009
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks130000G00.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 108 10 3226 := by
  have suffix : Floor 110 10 3226 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks130000G00.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 4160 9 102352 := by
  have suffix : Floor 4480 9 102352 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor011
  intro s hs hbig
  by_cases h : s < 4480
  · exact join017_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 3584 9 87386 := by
  have suffix : Floor 3648 9 87386 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor022
  intro s hs hbig
  by_cases h : s < 3648
  · exact SourceCoverChecks130000G00.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 3520 9 85330 := by
  have suffix : Floor 3584 9 85330 :=
    weaken (by decide) (by decide) floor016
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 3456 9 82916 := by
  have suffix : Floor 3520 9 82916 :=
    weaken (by decide) (by decide) floor015
  intro s hs hbig
  by_cases h : s < 3520
  · exact SourceCoverChecks130000G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 560 9 13055 := by
  have suffix : Floor 570 9 13055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor020
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks130000G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 550 9 12589 := by
  have suffix : Floor 560 9 12589 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 560
  · exact SourceCoverChecks130000G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 540 9 12048 := by
  have suffix : Floor 550 9 12048 :=
    weaken (by decide) (by decide) floor012
  intro s hs hbig
  by_cases h : s < 550
  · exact SourceCoverChecks130000G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 4160 8 81729 := by
  have suffix : Floor 4896 8 81729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor003
  intro s hs hbig
  by_cases h : s < 4896
  · exact join010_01 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 3584 8 70568 := by
  have suffix : Floor 3680 8 70568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor016
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks130000G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 3520 8 68488 := by
  have suffix : Floor 3584 8 68488 :=
    weaken (by decide) (by decide) floor009
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 3456 8 66720 := by
  have suffix : Floor 3520 8 66720 :=
    weaken (by decide) (by decide) floor008
  intro s hs hbig
  by_cases h : s < 3520
  · exact SourceCoverChecks130000G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 3456 7 49583 := by
  have suffix : Floor 3648 7 49583 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor013
  intro s hs hbig
  by_cases h : s < 3648
  · exact SourceCoverChecks130000G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 3584 6 40604 := by
  have suffix : Floor 4800 6 40604 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor000
  intro s hs hbig
  by_cases h : s < 4800
  · exact join005_02 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 3456 6 37189 := by
  have suffix : Floor 3584 6 37189 :=
    weaken (by decide) (by decide) floor005
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 3456 5 22168 :=
  of_prefix_tail (C := 10351) (by decide) (by decide) (by decide +kernel) join003_10
#print axioms floor003

theorem floor002 : Floor 3584 4 13055 := by
  have suffix : Floor 3648 4 13055 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor002
  intro s hs hbig
  by_cases h : s < 3648
  · exact SourceCoverChecks130000G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 3520 4 12589 := by
  have suffix : Floor 3584 4 12589 :=
    weaken (by decide) (by decide) floor002
  intro s hs hbig
  by_cases h : s < 3584
  · exact SourceCoverChecks130000G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 3456 4 12048 := by
  have suffix : Floor 3520 4 12048 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 3520
  · exact SourceCoverChecks130000G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors130000
