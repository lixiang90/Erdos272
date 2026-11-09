module

public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G00
public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G01
public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G02
public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G03
public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G04
public import Erdos272.Arithmetic.N250262.SourceCoverChecks250262G05
public import Erdos272.Arithmetic.N291012.SourceSuffixPilot3047

@[expose] public section

namespace JSP233.SourceFloors250262
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join015_00 : ∀ s, 4800 ≤ s → s < 5152 → 211690 ≤ physicalK s 12 :=
  append_cover SourceCoverChecks250262G00.bound0014 SourceCoverChecks250262G00.bound0015
#print axioms join015_00

theorem join021_00 : ∀ s, 790 ≤ s → s < 1500 → 46306 ≤ physicalK s 14 :=
  append_cover SourceCoverChecks250262G00.bound0021 SourceCoverChecks250262G00.bound0022
#print axioms join021_00

theorem floor172 : Floor 158 93 263600 := by
  have suffix : Floor 164 93 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor570
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks250262G05.bound0171 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor172

theorem floor171 : Floor 156 93 258232 := by
  have suffix : Floor 158 93 258232 :=
    weaken (by decide) (by decide) floor172
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G05.bound0170 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor171

theorem floor170 : Floor 153 92 248404 := by
  have suffix : Floor 164 92 248404 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor570
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks250262G05.bound0169 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor170

theorem floor169 : Floor 150 91 237924 := by
  have suffix : Floor 161 91 237924 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor567
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks250262G05.bound0168 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor169

theorem floor168 : Floor 158 87 236152 := by
  have suffix : Floor 169 87 236152 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor556
  intro s hs hbig
  by_cases h : s < 169
  · exact SourceCoverChecks250262G05.bound0167 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor168

theorem floor167 : Floor 153 86 222062 := by
  have suffix : Floor 164 86 222062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor554
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks250262G05.bound0166 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor167

theorem floor166 : Floor 156 85 223420 := by
  have suffix : Floor 164 85 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor554
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks250262G05.bound0165 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor166

theorem floor165 : Floor 150 85 211690 := by
  have suffix : Floor 156 85 211690 :=
    weaken (by decide) (by decide) floor166
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks250262G05.bound0164 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor165

theorem floor164 : Floor 158 79 202606 := by
  have suffix : Floor 175 79 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor530
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks250262G05.bound0163 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor164

theorem floor163 : Floor 150 79 188128 := by
  have suffix : Floor 158 79 188128 :=
    weaken (by decide) (by decide) floor164
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G05.bound0162 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor163

theorem floor162 : Floor 153 78 188020 := by
  have suffix : Floor 164 78 188020 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor526
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks250262G05.bound0161 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor162

theorem floor161 : Floor 156 77 191276 := by
  have suffix : Floor 169 77 191276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor529
  intro s hs hbig
  by_cases h : s < 169
  · exact SourceCoverChecks250262G05.bound0160 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor161

theorem floor160 : Floor 221 71 263600 := by
  have suffix : Floor 229 71 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor510
  intro s hs hbig
  by_cases h : s < 229
  · exact SourceCoverChecks250262G04.bound0159 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor160

theorem floor159 : Floor 150 71 159620 := by
  have suffix : Floor 161 71 159620 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor513
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks250262G04.bound0158 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor159

theorem floor158 : Floor 218 70 258232 := by
  have suffix : Floor 224 70 258232 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor509
  intro s hs hbig
  by_cases h : s < 224
  · exact SourceCoverChecks250262G04.bound0157 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor158

theorem floor157 : Floor 214 70 248404 := by
  have suffix : Floor 218 70 248404 :=
    weaken (by decide) (by decide) floor158
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks250262G04.bound0156 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor157

theorem floor156 : Floor 210 69 237924 := by
  have suffix : Floor 216 69 237924 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor508
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks250262G04.bound0155 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor156

theorem floor155 : Floor 158 69 163920 := by
  have suffix : Floor 175 69 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor485
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks250262G04.bound0154 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor155

theorem floor154 : Floor 156 69 161166 := by
  have suffix : Floor 158 69 161166 :=
    weaken (by decide) (by decide) floor155
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G04.bound0153 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor154

theorem floor153 : Floor 153 68 153380 := by
  have suffix : Floor 169 68 153380 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor484
  intro s hs hbig
  by_cases h : s < 169
  · exact SourceCoverChecks250262G04.bound0152 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor153

theorem floor152 : Floor 221 66 236152 := by
  have suffix : Floor 236 66 236152 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor492
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks250262G04.bound0151 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor152

theorem floor151 : Floor 214 66 222062 := by
  have suffix : Floor 221 66 222062 :=
    weaken (by decide) (by decide) floor152
  intro s hs hbig
  by_cases h : s < 221
  · exact SourceCoverChecks250262G04.bound0150 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor151

theorem floor150 : Floor 218 65 223420 := by
  have suffix : Floor 229 65 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor486
  intro s hs hbig
  by_cases h : s < 229
  · exact SourceCoverChecks250262G04.bound0149 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor150

theorem floor149 : Floor 210 65 211690 := by
  have suffix : Floor 218 65 211690 :=
    weaken (by decide) (by decide) floor150
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks250262G04.bound0148 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor149

theorem floor148 : Floor 221 61 202606 := by
  have suffix : Floor 239 61 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor460
  intro s hs hbig
  by_cases h : s < 239
  · exact SourceCoverChecks250262G04.bound0147 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor148

theorem floor147 : Floor 210 61 188128 := by
  have suffix : Floor 221 61 188128 :=
    weaken (by decide) (by decide) floor148
  intro s hs hbig
  by_cases h : s < 221
  · exact SourceCoverChecks250262G04.bound0146 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor147

theorem floor146 : Floor 218 59 191276 := by
  have suffix : Floor 232 59 191276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor453
  intro s hs hbig
  by_cases h : s < 232
  · exact SourceCoverChecks250262G04.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor146

theorem floor145 : Floor 214 59 188020 := by
  have suffix : Floor 218 59 188020 :=
    weaken (by decide) (by decide) floor146
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks250262G04.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 158 59 127638 := by
  have suffix : Floor 184 59 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor427
  intro s hs hbig
  by_cases h : s < 184
  · exact SourceCoverChecks250262G04.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 156 59 125500 := by
  have suffix : Floor 158 59 125500 :=
    weaken (by decide) (by decide) floor144
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G04.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 150 59 119268 := by
  have suffix : Floor 156 59 119268 :=
    weaken (by decide) (by decide) floor143
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks250262G04.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 153 58 119312 := by
  have suffix : Floor 180 58 119312 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor426
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks250262G04.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 316 56 263600 := by
  have suffix : Floor 328 56 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor440
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks250262G04.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 312 56 258232 := by
  have suffix : Floor 313 56 258232 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor446
  intro s hs hbig
  by_cases h : s < 313
  · exact SourceCoverChecks250262G04.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 306 55 248404 := by
  have suffix : Floor 328 55 248404 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor440
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks250262G04.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 300 55 237924 := by
  have suffix : Floor 302 55 237924 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor439
  intro s hs hbig
  by_cases h : s < 302
  · exact SourceCoverChecks250262G04.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 210 55 159620 := by
  have suffix : Floor 216 55 159620 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor437
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks250262G04.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 221 54 163920 := by
  have suffix : Floor 245 54 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor412
  intro s hs hbig
  by_cases h : s < 245
  · exact SourceCoverChecks250262G04.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 218 54 161166 := by
  have suffix : Floor 221 54 161166 :=
    weaken (by decide) (by decide) floor135
  intro s hs hbig
  by_cases h : s < 221
  · exact SourceCoverChecks250262G04.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 316 53 236152 := by
  have suffix : Floor 322 53 236152 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor429
  intro s hs hbig
  by_cases h : s < 322
  · exact SourceCoverChecks250262G04.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 214 53 153380 := by
  have suffix : Floor 236 53 153380 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor411
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks250262G04.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 306 52 222062 := by
  have suffix : Floor 328 52 222062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor413
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks250262G04.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 312 51 223420 := by
  have suffix : Floor 328 51 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor413
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks250262G04.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 300 51 211690 := by
  have suffix : Floor 312 51 211690 :=
    weaken (by decide) (by decide) floor130
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks250262G04.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 316 49 202606 := by
  have suffix : Floor 322 49 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor400
  intro s hs hbig
  by_cases h : s < 322
  · exact SourceCoverChecks250262G03.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 300 48 188128 := by
  have suffix : Floor 324 48 188128 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor384
  intro s hs hbig
  by_cases h : s < 324
  · exact SourceCoverChecks250262G03.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 312 47 191276 := by
  have suffix : Floor 324 47 191276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor384
  intro s hs hbig
  by_cases h : s < 324
  · exact SourceCoverChecks250262G03.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 221 47 127638 := by
  have suffix : Floor 257 47 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor356
  intro s hs hbig
  by_cases h : s < 257
  · exact SourceCoverChecks250262G03.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 218 47 125500 := by
  have suffix : Floor 221 47 125500 :=
    weaken (by decide) (by decide) floor125
  intro s hs hbig
  by_cases h : s < 221
  · exact SourceCoverChecks250262G03.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 214 47 119312 := by
  have suffix : Floor 218 47 119312 :=
    weaken (by decide) (by decide) floor124
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks250262G03.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 210 47 119268 := by
  have suffix : Floor 214 47 119268 :=
    weaken (by decide) (by decide) floor123
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks250262G03.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 158 47 86418 := by
  have suffix : Floor 210 47 86418 :=
    weaken (by decide) (by decide) floor122
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks250262G03.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 156 47 84454 := by
  have suffix : Floor 158 47 84454 :=
    weaken (by decide) (by decide) floor121
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G03.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 153 47 83678 := by
  have suffix : Floor 156 47 83678 :=
    weaken (by decide) (by decide) floor120
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks250262G03.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 150 47 80802 := by
  have suffix : Floor 153 47 80802 :=
    weaken (by decide) (by decide) floor119
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks250262G03.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 474 44 263600 := by
  have suffix : Floor 492 44 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor365
  intro s hs hbig
  by_cases h : s < 492
  · exact SourceCoverChecks250262G03.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 468 44 258232 := by
  have suffix : Floor 474 44 258232 :=
    weaken (by decide) (by decide) floor117
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks250262G03.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 459 44 248404 := by
  have suffix : Floor 468 44 248404 :=
    weaken (by decide) (by decide) floor116
  intro s hs hbig
  by_cases h : s < 468
  · exact SourceCoverChecks250262G03.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 316 44 163920 := by
  have suffix : Floor 322 44 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor364
  intro s hs hbig
  by_cases h : s < 322
  · exact SourceCoverChecks250262G03.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 312 44 161166 := by
  have suffix : Floor 316 44 161166 :=
    weaken (by decide) (by decide) floor114
  intro s hs hbig
  by_cases h : s < 316
  · exact SourceCoverChecks250262G03.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 300 44 159620 := by
  have suffix : Floor 312 44 159620 :=
    weaken (by decide) (by decide) floor113
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks250262G03.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 450 43 237924 := by
  have suffix : Floor 483 43 237924 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor351
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G03.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 306 43 153380 := by
  have suffix : Floor 338 43 153380 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor340
  intro s hs hbig
  by_cases h : s < 338
  · exact SourceCoverChecks250262G03.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 474 42 236152 := by
  have suffix : Floor 483 42 236152 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor351
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G03.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 468 41 223420 := by
  have suffix : Floor 492 41 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor342
  intro s hs hbig
  by_cases h : s < 492
  · exact SourceCoverChecks250262G03.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 459 41 222062 := by
  have suffix : Floor 468 41 222062 :=
    weaken (by decide) (by decide) floor108
  intro s hs hbig
  by_cases h : s < 468
  · exact SourceCoverChecks250262G03.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 450 41 211690 := by
  have suffix : Floor 459 41 211690 :=
    weaken (by decide) (by decide) floor107
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks250262G03.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 474 39 202606 := by
  have suffix : Floor 478 39 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor323
  intro s hs hbig
  by_cases h : s < 478
  · exact SourceCoverChecks250262G03.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 468 38 191276 := by
  have suffix : Floor 468 38 191276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor314
  exact suffix
#print axioms floor104

theorem floor103 : Floor 450 38 188128 := by
  have suffix : Floor 464 38 188128 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor314
  intro s hs hbig
  by_cases h : s < 464
  · exact SourceCoverChecks250262G03.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 316 38 127638 := by
  have suffix : Floor 368 38 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor282
  intro s hs hbig
  by_cases h : s < 368
  · exact SourceCoverChecks250262G03.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 312 38 125500 := by
  have suffix : Floor 316 38 125500 :=
    weaken (by decide) (by decide) floor102
  intro s hs hbig
  by_cases h : s < 316
  · exact SourceCoverChecks250262G03.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 306 38 119312 := by
  have suffix : Floor 312 38 119312 :=
    weaken (by decide) (by decide) floor101
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks250262G03.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 300 38 119268 := by
  have suffix : Floor 306 38 119268 :=
    weaken (by decide) (by decide) floor100
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks250262G03.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 221 38 86418 := by
  have suffix : Floor 300 38 86418 :=
    weaken (by decide) (by decide) floor099
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks250262G03.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 218 38 84454 := by
  have suffix : Floor 218 38 84454 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor313
  exact suffix
#print axioms floor097

theorem floor096 : Floor 214 38 83678 := by
  have suffix : Floor 216 38 83678 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor313
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks250262G03.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 210 38 80802 := by
  have suffix : Floor 214 38 80802 :=
    weaken (by decide) (by decide) floor096
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks250262G03.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 474 35 163920 := by
  have suffix : Floor 483 35 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor284
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G02.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 468 35 161166 := by
  have suffix : Floor 474 35 161166 :=
    weaken (by decide) (by decide) floor094
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks250262G02.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 450 35 159620 := by
  have suffix : Floor 468 35 159620 :=
    weaken (by decide) (by decide) floor093
  intro s hs hbig
  by_cases h : s < 468
  · exact SourceCoverChecks250262G02.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 790 34 263600 := by
  have suffix : Floor 805 34 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor275
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G02.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 780 34 258232 := by
  have suffix : Floor 790 34 258232 :=
    weaken (by decide) (by decide) floor091
  intro s hs hbig
  by_cases h : s < 790
  · exact SourceCoverChecks250262G02.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 459 34 153380 := by
  have suffix : Floor 507 34 153380 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor260
  intro s hs hbig
  by_cases h : s < 507
  · exact SourceCoverChecks250262G02.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 153 34 46910 := by
  have suffix : Floor 161 34 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor266
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks250262G02.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 765 33 248404 := by
  have suffix : Floor 820 33 248404 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor263
  intro s hs hbig
  by_cases h : s < 820
  · exact SourceCoverChecks250262G02.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 750 33 237924 := by
  have suffix : Floor 765 33 237924 :=
    weaken (by decide) (by decide) floor087
  intro s hs hbig
  by_cases h : s < 765
  · exact SourceCoverChecks250262G02.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 158 33 46306 := by
  have suffix : Floor 225 33 46306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor206
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks250262G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 150 33 43412 := by
  have suffix : Floor 158 33 43412 :=
    weaken (by decide) (by decide) floor085
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks250262G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 790 32 236152 := by
  have suffix : Floor 845 32 236152 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor247
  intro s hs hbig
  by_cases h : s < 845
  · exact SourceCoverChecks250262G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 765 32 222062 := by
  have suffix : Floor 790 32 222062 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 790
  · exact SourceCoverChecks250262G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 156 32 43112 := by
  have suffix : Floor 225 32 43112 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor206
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks250262G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 780 31 223420 := by
  have suffix : Floor 820 31 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor246
  intro s hs hbig
  by_cases h : s < 820
  · exact SourceCoverChecks250262G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 750 31 211690 := by
  have suffix : Floor 780 31 211690 :=
    weaken (by decide) (by decide) floor080
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks250262G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 474 31 127638 := by
  have suffix : Floor 483 31 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor243
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 468 31 125500 := by
  have suffix : Floor 474 31 125500 :=
    weaken (by decide) (by decide) floor078
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks250262G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 316 31 86418 := by
  have suffix : Floor 464 31 86418 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor210
  intro s hs hbig
  by_cases h : s < 464
  · exact SourceCoverChecks250262G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 312 31 84454 := by
  have suffix : Floor 313 31 84454 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor242
  intro s hs hbig
  by_cases h : s < 313
  · exact SourceCoverChecks250262G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 306 31 83678 := by
  have suffix : Floor 312 31 83678 :=
    weaken (by decide) (by decide) floor075
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks250262G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 300 31 80802 := by
  have suffix : Floor 306 31 80802 :=
    weaken (by decide) (by decide) floor074
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks250262G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 790 30 202606 := by
  have suffix : Floor 805 30 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor235
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 459 30 119312 := by
  have suffix : Floor 540 30 119312 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor211
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks250262G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 450 30 119268 := by
  have suffix : Floor 459 30 119268 :=
    weaken (by decide) (by decide) floor071
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks250262G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 780 29 191276 := by
  have suffix : Floor 845 29 191276 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor223
  intro s hs hbig
  by_cases h : s < 845
  · exact SourceCoverChecks250262G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 750 29 188128 := by
  have suffix : Floor 780 29 188128 :=
    weaken (by decide) (by decide) floor069
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks250262G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 214 28 46910 := by
  have suffix : Floor 225 28 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor206
  intro s hs hbig
  by_cases h : s < 225
  · exact SourceCoverChecks250262G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 790 27 163920 := by
  have suffix : Floor 805 27 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor201
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 780 27 161166 := by
  have suffix : Floor 790 27 161166 :=
    weaken (by decide) (by decide) floor066
  intro s hs hbig
  by_cases h : s < 790
  · exact SourceCoverChecks250262G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 750 27 159620 := by
  have suffix : Floor 780 27 159620 :=
    weaken (by decide) (by decide) floor065
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks250262G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 210 27 43412 := by
  have suffix : Floor 322 27 43412 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor146
  intro s hs hbig
  by_cases h : s < 322
  · exact SourceCoverChecks250262G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 765 26 153380 := by
  have suffix : Floor 845 26 153380 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor175
  intro s hs hbig
  by_cases h : s < 845
  · exact SourceCoverChecks250262G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 474 25 86418 := by
  have suffix : Floor 696 25 86418 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor149
  intro s hs hbig
  by_cases h : s < 696
  · exact SourceCoverChecks250262G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 468 25 84454 := by
  have suffix : Floor 474 25 84454 :=
    weaken (by decide) (by decide) floor061
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks250262G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 459 25 83678 := by
  have suffix : Floor 468 25 83678 :=
    weaken (by decide) (by decide) floor060
  intro s hs hbig
  by_cases h : s < 468
  · exact SourceCoverChecks250262G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 450 25 80802 := by
  have suffix : Floor 459 25 80802 :=
    weaken (by decide) (by decide) floor059
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks250262G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 1580 24 263600 := by
  have suffix : Floor 1610 24 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor164
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 1560 24 258232 := by
  have suffix : Floor 1580 24 258232 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 1580
  · exact SourceCoverChecks250262G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 1530 24 248404 := by
  have suffix : Floor 1560 24 248404 :=
    weaken (by decide) (by decide) floor056
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 790 24 127638 := by
  have suffix : Floor 805 24 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor161
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 1500 23 237924 := by
  have suffix : Floor 1610 23 237924 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor154
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 780 23 125500 := by
  have suffix : Floor 900 23 125500 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor140
  intro s hs hbig
  by_cases h : s < 900
  · exact SourceCoverChecks250262G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 765 23 119312 := by
  have suffix : Floor 780 23 119312 :=
    weaken (by decide) (by decide) floor052
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks250262G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 750 23 119268 := by
  have suffix : Floor 765 23 119268 :=
    weaken (by decide) (by decide) floor051
  intro s hs hbig
  by_cases h : s < 765
  · exact SourceCoverChecks250262G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 306 23 46910 := by
  have suffix : Floor 322 23 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor146
  intro s hs hbig
  by_cases h : s < 322
  · exact SourceCoverChecks250262G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 300 23 43412 := by
  have suffix : Floor 306 23 43412 :=
    weaken (by decide) (by decide) floor049
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks250262G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 1560 22 223420 := by
  have suffix : Floor 1640 22 223420 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor143
  intro s hs hbig
  by_cases h : s < 1640
  · exact SourceCoverChecks250262G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 1530 22 222062 := by
  have suffix : Floor 1560 22 222062 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 1500 22 211690 := by
  have suffix : Floor 1530 22 211690 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 1530
  · exact SourceCoverChecks250262G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 312 22 43112 := by
  have suffix : Floor 483 22 43112 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor110
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 1580 21 202606 := by
  have suffix : Floor 1610 21 202606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor132
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 1560 21 191276 := by
  have suffix : Floor 1580 21 191276 :=
    weaken (by decide) (by decide) floor043
  intro s hs hbig
  by_cases h : s < 1580
  · exact SourceCoverChecks250262G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 1500 21 188128 := by
  have suffix : Floor 1560 21 188128 :=
    weaken (by decide) (by decide) floor042
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 790 20 86418 := by
  have suffix : Floor 805 20 86418 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor120
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 1580 19 163920 := by
  have suffix : Floor 1610 19 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor114
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 1560 19 161166 := by
  have suffix : Floor 1580 19 161166 :=
    weaken (by decide) (by decide) floor039
  intro s hs hbig
  by_cases h : s < 1580
  · exact SourceCoverChecks250262G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 1500 19 159620 := by
  have suffix : Floor 1560 19 159620 :=
    weaken (by decide) (by decide) floor038
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 780 19 84454 := by
  have suffix : Floor 1080 19 84454 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor096
  intro s hs hbig
  by_cases h : s < 1080
  · exact SourceCoverChecks250262G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 765 19 83678 := by
  have suffix : Floor 780 19 83678 :=
    weaken (by decide) (by decide) floor036
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks250262G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 750 19 80802 := by
  have suffix : Floor 765 19 80802 :=
    weaken (by decide) (by decide) floor035
  intro s hs hbig
  by_cases h : s < 765
  · exact SourceCoverChecks250262G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 459 19 46910 := by
  have suffix : Floor 483 19 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor110
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks250262G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 474 18 46306 := by
  have suffix : Floor 805 18 46306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor067
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 450 18 43412 := by
  have suffix : Floor 474 18 43412 :=
    weaken (by decide) (by decide) floor032
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks250262G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 1580 17 127638 := by
  have suffix : Floor 1610 17 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor098
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 1560 17 125500 := by
  have suffix : Floor 1580 17 125500 :=
    weaken (by decide) (by decide) floor030
  intro s hs hbig
  by_cases h : s < 1580
  · exact SourceCoverChecks250262G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 1500 17 119268 := by
  have suffix : Floor 1560 17 119268 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 1530 16 119312 := by
  have suffix : Floor 1800 16 119312 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor085
  intro s hs hbig
  by_cases h : s < 1800
  · exact SourceCoverChecks250262G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 765 15 46910 := by
  have suffix : Floor 805 15 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor067
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks250262G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 1580 14 86418 := by
  have suffix : Floor 1610 14 86418 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor056
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 1560 14 84454 := by
  have suffix : Floor 1580 14 84454 :=
    weaken (by decide) (by decide) floor025
  intro s hs hbig
  by_cases h : s < 1580
  · exact SourceCoverChecks250262G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 1530 14 83678 := by
  have suffix : Floor 1560 14 83678 :=
    weaken (by decide) (by decide) floor024
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks250262G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 1500 14 80802 := by
  have suffix : Floor 1530 14 80802 :=
    weaken (by decide) (by decide) floor023
  intro s hs hbig
  by_cases h : s < 1530
  · exact SourceCoverChecks250262G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 790 14 46306 := by
  have suffix : Floor 1500 14 46306 :=
    weaken (by decide) (by decide) floor022
  intro s hs hbig
  by_cases h : s < 1500
  · exact join021_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 750 14 43412 := by
  have suffix : Floor 790 14 43412 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 790
  · exact SourceCoverChecks250262G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 5056 13 263600 := by
  have suffix : Floor 5248 13 263600 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor050
  intro s hs hbig
  by_cases h : s < 5248
  · exact SourceCoverChecks250262G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 4992 13 258232 := by
  have suffix : Floor 5056 13 258232 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 5056
  · exact SourceCoverChecks250262G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 4896 13 248404 := by
  have suffix : Floor 4992 13 248404 :=
    weaken (by decide) (by decide) floor018
  intro s hs hbig
  by_cases h : s < 4992
  · exact SourceCoverChecks250262G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 4800 13 237924 := by
  have suffix : Floor 4896 13 237924 :=
    weaken (by decide) (by decide) floor017
  intro s hs hbig
  by_cases h : s < 4896
  · exact SourceCoverChecks250262G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 4800 12 211690 := by
  have suffix : Floor 5152 12 211690 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor042
  intro s hs hbig
  by_cases h : s < 5152
  · exact join015_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 5056 11 163920 := by
  have suffix : Floor 5152 11 163920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor033
  intro s hs hbig
  by_cases h : s < 5152
  · exact SourceCoverChecks250262G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 4992 11 161166 := by
  have suffix : Floor 5056 11 161166 :=
    weaken (by decide) (by decide) floor014
  intro s hs hbig
  by_cases h : s < 5056
  · exact SourceCoverChecks250262G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 4800 11 159620 := by
  have suffix : Floor 4992 11 159620 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 4992
  · exact SourceCoverChecks250262G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 5056 10 127638 := by
  have suffix : Floor 5152 10 127638 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor020
  intro s hs hbig
  by_cases h : s < 5152
  · exact SourceCoverChecks250262G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 4992 10 125500 := by
  have suffix : Floor 5056 10 125500 :=
    weaken (by decide) (by decide) floor011
  intro s hs hbig
  by_cases h : s < 5056
  · exact SourceCoverChecks250262G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 4800 10 119268 := by
  have suffix : Floor 4992 10 119268 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 4992
  · exact SourceCoverChecks250262G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 1530 10 46910 := by
  have suffix : Floor 1610 10 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor019
  intro s hs hbig
  by_cases h : s < 1610
  · exact SourceCoverChecks250262G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 1500 10 43412 := by
  have suffix : Floor 1530 10 43412 :=
    weaken (by decide) (by decide) floor008
  intro s hs hbig
  by_cases h : s < 1530
  · exact SourceCoverChecks250262G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 4896 9 119312 :=
  SourceSuffixPilot3047.extended_floor
#print axioms floor006

theorem floor005 : Floor 5056 8 86418 := by
  have suffix : Floor 5152 8 86418 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor010
  intro s hs hbig
  by_cases h : s < 5152
  · exact SourceCoverChecks250262G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 4992 8 84454 := by
  have suffix : Floor 5056 8 84454 :=
    weaken (by decide) (by decide) floor005
  intro s hs hbig
  by_cases h : s < 5056
  · exact SourceCoverChecks250262G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 4896 8 83678 := by
  have suffix : Floor 4992 8 83678 :=
    weaken (by decide) (by decide) floor004
  intro s hs hbig
  by_cases h : s < 4992
  · exact SourceCoverChecks250262G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 4800 8 80802 := by
  have suffix : Floor 4896 8 80802 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 4896
  · exact SourceCoverChecks250262G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 4896 6 46910 := by
  have suffix : Floor 5152 6 46910 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor000
  intro s hs hbig
  by_cases h : s < 5152
  · exact SourceCoverChecks250262G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 4800 6 43412 := by
  have suffix : Floor 4896 6 43412 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 4896
  · exact SourceCoverChecks250262G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors250262
