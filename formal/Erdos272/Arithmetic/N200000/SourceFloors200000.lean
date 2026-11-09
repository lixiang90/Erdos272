module

public import Erdos272.Arithmetic.N200000.SourceCoverChecks200000G00
public import Erdos272.Arithmetic.N200000.SourceCoverChecks200000G01
public import Erdos272.Arithmetic.N200000.SourceCoverChecks200000G02
public import Erdos272.Arithmetic.N200000.SourceCoverChecks200000G03
public import Erdos272.Arithmetic.N200000.SourceCoverChecks200000G04
public import Erdos272.Arithmetic.N233811.SourceFloors233811

@[expose] public section

namespace JSP233.SourceFloors200000
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join004_00 : ∀ s, 4384 ≤ s → s < 5002 → 64296 ≤ physicalK s 7 :=
  append_cover SourceCoverChecks200000G00.bound0004 SourceCoverChecks200000G00.bound0005
#print axioms join004_00

theorem join004_01 : ∀ s, 5002 ≤ s → s < 5760 → 64296 ≤ physicalK s 7 :=
  append_cover SourceCoverChecks200000G00.bound0006 SourceCoverChecks200000G00.bound0007
#print axioms join004_01

theorem join004_02 : ∀ s, 4384 ≤ s → s < 5760 → 64296 ≤ physicalK s 7 :=
  append_cover join004_00 join004_01
#print axioms join004_02

theorem join023_00 : ∀ s, 4480 ≤ s → s < 4800 → 193464 ≤ physicalK s 12 :=
  append_cover SourceCoverChecks200000G00.bound0026 SourceCoverChecks200000G00.bound0027
#print axioms join023_00

theorem floor143 : Floor 140 85 193464 := by
  have suffix : Floor 150 85 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor165
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks200000G04.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 137 84 184410 := by
  have suffix : Floor 145 84 184410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor081
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 134 83 175390 := by
  have suffix : Floor 145 83 175390 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor081
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 140 81 178632 := by
  have suffix : Floor 150 81 178632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor163
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks200000G04.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 137 80 170058 := by
  have suffix : Floor 147 80 170058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor080
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks200000G04.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 134 79 161446 := by
  have suffix : Floor 145 79 161446 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor079
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 140 75 156978 := by
  have suffix : Floor 145 75 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor079
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 137 74 148320 := by
  have suffix : Floor 145 74 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor079
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 134 73 141584 := by
  have suffix : Floor 150 73 141584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor159
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks200000G04.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 140 67 131774 := by
  have suffix : Floor 145 67 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor076
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 134 67 124058 := by
  have suffix : Floor 140 67 124058 :=
    weaken (by decide) (by decide) floor134
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks200000G04.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 137 66 125252 := by
  have suffix : Floor 145 66 125252 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor076
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G04.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 196 65 193464 := by
  have suffix : Floor 198 65 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor491
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks200000G04.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 191 64 184410 := by
  have suffix : Floor 203 64 184410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor075
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G04.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 187 63 175390 := by
  have suffix : Floor 203 63 175390 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor075
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G04.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 196 62 178632 := by
  have suffix : Floor 203 62 178632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor075
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G04.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 191 61 170058 := by
  have suffix : Floor 205 61 170058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor074
  intro s hs hbig
  by_cases h : s < 205
  · exact SourceCoverChecks200000G04.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 187 60 161446 := by
  have suffix : Floor 203 60 161446 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor073
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G03.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 140 59 108208 := by
  have suffix : Floor 148 59 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor030
  intro s hs hbig
  by_cases h : s < 148
  · exact SourceCoverChecks200000G03.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 137 58 102230 := by
  have suffix : Floor 145 58 102230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor071
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G03.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 196 57 156978 := by
  have suffix : Floor 203 57 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor073
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G03.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 134 57 96548 := by
  have suffix : Floor 145 57 96548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor071
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G03.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 191 56 148320 := by
  have suffix : Floor 207 56 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor434
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks200000G03.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 187 56 141584 := by
  have suffix : Floor 189 56 141584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor444
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks200000G03.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 196 52 131774 := by
  have suffix : Floor 198 52 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor418
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks200000G03.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 191 52 125252 := by
  have suffix : Floor 196 52 125252 :=
    weaken (by decide) (by decide) floor119
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks200000G03.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 187 52 124058 := by
  have suffix : Floor 191 52 124058 :=
    weaken (by decide) (by decide) floor118
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks200000G03.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 280 51 193464 := by
  have suffix : Floor 300 51 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor129
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks200000G03.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 274 50 184410 := by
  have suffix : Floor 290 50 184410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor067
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G03.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 268 50 175390 := by
  have suffix : Floor 274 50 175390 :=
    weaken (by decide) (by decide) floor115
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks200000G03.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 280 49 178632 := by
  have suffix : Floor 300 49 178632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor127
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks200000G03.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 274 48 170058 := by
  have suffix : Floor 294 48 170058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor066
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks200000G03.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 268 47 161446 := by
  have suffix : Floor 290 47 161446 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor065
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G03.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 196 47 108208 := by
  have suffix : Floor 207 47 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor027
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks200000G03.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 280 46 156978 := by
  have suffix : Floor 290 46 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor065
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G03.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 191 46 102230 := by
  have suffix : Floor 203 46 102230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor063
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G03.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 274 45 148320 := by
  have suffix : Floor 289 45 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor363
  intro s hs hbig
  by_cases h : s < 289
  · exact SourceCoverChecks200000G03.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 187 45 96548 := by
  have suffix : Floor 203 45 96548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor063
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks200000G03.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 140 45 69264 := by
  have suffix : Floor 145 45 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor061
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G03.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 268 44 141584 := by
  have suffix : Floor 289 44 141584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor363
  intro s hs hbig
  by_cases h : s < 289
  · exact SourceCoverChecks200000G03.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 137 44 64296 := by
  have suffix : Floor 145 44 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor061
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks200000G03.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 134 43 60652 := by
  have suffix : Floor 180 43 60652 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor312
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks200000G03.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 280 42 131774 := by
  have suffix : Floor 280 42 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor348
  exact suffix
#print axioms floor101

theorem floor100 : Floor 420 41 193464 := by
  have suffix : Floor 450 41 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor106
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks200000G03.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 274 41 125252 := by
  have suffix : Floor 290 41 125252 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor058
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G03.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 268 41 124058 := by
  have suffix : Floor 274 41 124058 :=
    weaken (by decide) (by decide) floor099
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks200000G03.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 411 40 184410 := by
  have suffix : Floor 435 40 184410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor057
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks200000G03.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 420 39 178632 := by
  have suffix : Floor 435 39 178632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor057
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks200000G03.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 402 39 175390 := by
  have suffix : Floor 420 39 175390 :=
    weaken (by decide) (by decide) floor096
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks200000G03.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 411 38 170058 := by
  have suffix : Floor 441 38 170058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor056
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks200000G03.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 402 38 161446 := by
  have suffix : Floor 411 38 161446 :=
    weaken (by decide) (by decide) floor094
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks200000G02.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 280 38 108208 := by
  have suffix : Floor 296 38 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor023
  intro s hs hbig
  by_cases h : s < 296
  · exact SourceCoverChecks200000G02.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 420 37 156978 := by
  have suffix : Floor 432 37 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor302
  intro s hs hbig
  by_cases h : s < 432
  · exact SourceCoverChecks200000G02.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 274 37 102230 := by
  have suffix : Floor 290 37 102230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor053
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G02.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 196 37 69264 := by
  have suffix : Floor 198 37 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor291
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks200000G02.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 411 36 148320 := by
  have suffix : Floor 414 36 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor293
  intro s hs hbig
  by_cases h : s < 414
  · exact SourceCoverChecks200000G02.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 268 36 96548 := by
  have suffix : Floor 290 36 96548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor053
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G02.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 191 36 64296 := by
  have suffix : Floor 198 36 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor291
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks200000G02.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 402 35 141584 := by
  have suffix : Floor 450 35 141584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor092
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks200000G02.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 187 35 60652 := by
  have suffix : Floor 252 35 60652 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor241
  intro s hs hbig
  by_cases h : s < 252
  · exact SourceCoverChecks200000G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 420 33 131774 := by
  have suffix : Floor 435 33 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor050
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks200000G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 411 33 125252 := by
  have suffix : Floor 420 33 125252 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks200000G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 402 33 124058 := by
  have suffix : Floor 411 33 124058 :=
    weaken (by decide) (by decide) floor082
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks200000G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 700 31 193464 := by
  have suffix : Floor 700 31 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor244
  exact suffix
#print axioms floor080

theorem floor079 : Floor 140 31 35244 := by
  have suffix : Floor 147 31 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor046
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks200000G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 137 31 35000 := by
  have suffix : Floor 140 31 35000 :=
    weaken (by decide) (by decide) floor079
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks200000G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 134 31 33540 := by
  have suffix : Floor 137 31 33540 :=
    weaken (by decide) (by decide) floor078
  intro s hs hbig
  by_cases h : s < 137
  · exact SourceCoverChecks200000G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 685 30 184410 := by
  have suffix : Floor 725 30 184410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor047
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks200000G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 670 30 175390 := by
  have suffix : Floor 685 30 175390 :=
    weaken (by decide) (by decide) floor076
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 420 30 108208 := by
  have suffix : Floor 444 30 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor017
  intro s hs hbig
  by_cases h : s < 444
  · exact SourceCoverChecks200000G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 411 30 102230 := by
  have suffix : Floor 420 30 102230 :=
    weaken (by decide) (by decide) floor074
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks200000G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 280 30 69264 := by
  have suffix : Floor 280 30 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor230
  exact suffix
#print axioms floor072

theorem floor071 : Floor 685 29 170058 := by
  have suffix : Floor 735 29 170058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor040
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks200000G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 670 29 161446 := by
  have suffix : Floor 685 29 161446 :=
    weaken (by decide) (by decide) floor071
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 402 29 96548 := by
  have suffix : Floor 435 29 96548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor043
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks200000G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 274 29 64296 := by
  have suffix : Floor 290 29 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor041
  intro s hs hbig
  by_cases h : s < 290
  · exact SourceCoverChecks200000G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 268 29 60652 := by
  have suffix : Floor 274 29 60652 :=
    weaken (by decide) (by decide) floor068
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks200000G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 700 28 156978 := by
  have suffix : Floor 725 28 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor039
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks200000G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 685 27 148320 := by
  have suffix : Floor 750 27 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor064
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks200000G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 670 27 141584 := by
  have suffix : Floor 685 27 141584 :=
    weaken (by decide) (by decide) floor065
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 196 26 35244 := by
  have suffix : Floor 205 26 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor037
  intro s hs hbig
  by_cases h : s < 205
  · exact SourceCoverChecks200000G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 191 26 35000 := by
  have suffix : Floor 196 26 35000 :=
    weaken (by decide) (by decide) floor063
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks200000G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 187 26 33540 := by
  have suffix : Floor 191 26 33540 :=
    weaken (by decide) (by decide) floor062
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks200000G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 700 25 131774 := by
  have suffix : Floor 725 25 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor038
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks200000G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 685 25 125252 := by
  have suffix : Floor 700 25 125252 :=
    weaken (by decide) (by decide) floor060
  intro s hs hbig
  by_cases h : s < 700
  · exact SourceCoverChecks200000G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 670 25 124058 := by
  have suffix : Floor 685 25 124058 :=
    weaken (by decide) (by decide) floor059
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 420 24 69264 := by
  have suffix : Floor 435 24 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor034
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks200000G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 700 23 108208 := by
  have suffix : Floor 740 23 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor013
  intro s hs hbig
  by_cases h : s < 740
  · exact SourceCoverChecks200000G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 685 23 102230 := by
  have suffix : Floor 696 23 102230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor149
  intro s hs hbig
  by_cases h : s < 696
  · exact SourceCoverChecks200000G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 411 23 64296 := by
  have suffix : Floor 540 23 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor128
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks200000G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 402 23 60652 := by
  have suffix : Floor 411 23 60652 :=
    weaken (by decide) (by decide) floor054
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks200000G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 1400 22 193464 := by
  have suffix : Floor 1500 22 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor045
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks200000G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 1370 22 184410 := by
  have suffix : Floor 1400 22 184410 :=
    weaken (by decide) (by decide) floor052
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 670 22 96548 := by
  have suffix : Floor 717 22 96548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor139
  intro s hs hbig
  by_cases h : s < 717
  · exact SourceCoverChecks200000G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 1400 21 178632 := by
  have suffix : Floor 1450 21 178632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor029
  intro s hs hbig
  by_cases h : s < 1450
  · exact SourceCoverChecks200000G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 1340 21 175390 := by
  have suffix : Floor 1400 21 175390 :=
    weaken (by decide) (by decide) floor049
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 280 21 35244 := by
  have suffix : Floor 294 21 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor028
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks200000G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 274 21 35000 := by
  have suffix : Floor 280 21 35000 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 280
  · exact SourceCoverChecks200000G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 268 21 33540 := by
  have suffix : Floor 274 21 33540 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks200000G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 1340 20 161446 := by
  have suffix : Floor 1450 20 161446 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor025
  intro s hs hbig
  by_cases h : s < 1450
  · exact SourceCoverChecks200000G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 1370 19 148320 := by
  have suffix : Floor 1500 19 148320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor037
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks200000G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 1340 19 141584 := by
  have suffix : Floor 1370 19 141584 :=
    weaken (by decide) (by decide) floor043
  intro s hs hbig
  by_cases h : s < 1370
  · exact SourceCoverChecks200000G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 700 19 69264 := by
  have suffix : Floor 725 19 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor022
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks200000G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 1400 18 131774 := by
  have suffix : Floor 1450 18 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor024
  intro s hs hbig
  by_cases h : s < 1450
  · exact SourceCoverChecks200000G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 1370 18 125252 := by
  have suffix : Floor 1400 18 125252 :=
    weaken (by decide) (by decide) floor040
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 1340 18 124058 := by
  have suffix : Floor 1370 18 124058 :=
    weaken (by decide) (by decide) floor039
  intro s hs hbig
  by_cases h : s < 1370
  · exact SourceCoverChecks200000G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 685 18 64296 := by
  have suffix : Floor 725 18 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor022
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks200000G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 670 18 60652 := by
  have suffix : Floor 685 18 60652 :=
    weaken (by decide) (by decide) floor037
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 420 17 35244 := by
  have suffix : Floor 441 17 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor021
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks200000G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 411 17 35000 := by
  have suffix : Floor 420 17 35000 :=
    weaken (by decide) (by decide) floor035
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks200000G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 402 17 33540 := by
  have suffix : Floor 411 17 33540 :=
    weaken (by decide) (by decide) floor034
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks200000G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 1400 16 108208 := by
  have suffix : Floor 1480 16 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor008
  intro s hs hbig
  by_cases h : s < 1480
  · exact SourceCoverChecks200000G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 1370 16 102230 := by
  have suffix : Floor 1400 16 102230 :=
    weaken (by decide) (by decide) floor032
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 1340 16 96548 := by
  have suffix : Floor 1370 16 96548 :=
    weaken (by decide) (by decide) floor031
  intro s hs hbig
  by_cases h : s < 1370
  · exact SourceCoverChecks200000G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 1400 13 69264 := by
  have suffix : Floor 1450 13 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor014
  intro s hs hbig
  by_cases h : s < 1450
  · exact SourceCoverChecks200000G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 1370 13 64296 := by
  have suffix : Floor 1400 13 64296 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 1340 13 60652 := by
  have suffix : Floor 1370 13 60652 :=
    weaken (by decide) (by decide) floor028
  intro s hs hbig
  by_cases h : s < 1370
  · exact SourceCoverChecks200000G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 700 13 35244 := by
  have suffix : Floor 735 13 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor013
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks200000G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 685 13 35000 := by
  have suffix : Floor 700 13 35000 :=
    weaken (by decide) (by decide) floor026
  intro s hs hbig
  by_cases h : s < 700
  · exact SourceCoverChecks200000G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 670 13 33540 := by
  have suffix : Floor 685 13 33540 :=
    weaken (by decide) (by decide) floor025
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks200000G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 4480 12 193464 := by
  have suffix : Floor 4800 12 193464 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor015
  intro s hs hbig
  by_cases h : s < 4800
  · exact join023_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 4384 12 184410 := by
  have suffix : Floor 4480 12 184410 :=
    weaken (by decide) (by decide) floor023
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks200000G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 4288 12 175390 := by
  have suffix : Floor 4384 12 175390 :=
    weaken (by decide) (by decide) floor022
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 4480 11 156978 := by
  have suffix : Floor 4640 11 156978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor009
  intro s hs hbig
  by_cases h : s < 4640
  · exact SourceCoverChecks200000G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 4384 11 148320 := by
  have suffix : Floor 4480 11 148320 :=
    weaken (by decide) (by decide) floor020
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks200000G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 4288 11 141584 := by
  have suffix : Floor 4384 11 141584 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 4480 10 131774 := by
  have suffix : Floor 4640 10 131774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor008
  intro s hs hbig
  by_cases h : s < 4640
  · exact SourceCoverChecks200000G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 4384 10 125252 := by
  have suffix : Floor 4480 10 125252 :=
    weaken (by decide) (by decide) floor017
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks200000G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 4288 10 124058 := by
  have suffix : Floor 4384 10 124058 :=
    weaken (by decide) (by decide) floor016
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 1370 10 35000 := by
  have suffix : Floor 1450 10 35000 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor004
  intro s hs hbig
  by_cases h : s < 1450
  · exact SourceCoverChecks200000G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 140 10 3700 :=
  of_prefix_tail (C := 481) (by decide) (by decide) (by decide +kernel) SourceCoverChecks200000G00.bound0016
#print axioms floor013

theorem floor012 : Floor 137 10 3520 := by
  have suffix : Floor 140 10 3520 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks200000G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 4480 9 108208 := by
  have suffix : Floor 4736 9 108208 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor002
  intro s hs hbig
  by_cases h : s < 4736
  · exact SourceCoverChecks200000G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 4384 9 102230 := by
  have suffix : Floor 4480 9 102230 :=
    weaken (by decide) (by decide) floor011
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks200000G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 4288 9 96548 := by
  have suffix : Floor 4384 9 96548 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 1400 9 35244 := by
  have suffix : Floor 1470 9 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor005
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks200000G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 1340 9 33540 := by
  have suffix : Floor 1400 9 33540 :=
    weaken (by decide) (by decide) floor008
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks200000G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 134 9 3402 :=
  of_prefix_tail (C := 539) (by decide) (by decide) (by decide +kernel) SourceCoverChecks200000G00.bound0009
#print axioms floor006

theorem floor005 : Floor 4480 8 69264 := by
  have suffix : Floor 4640 8 69264 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor002
  intro s hs hbig
  by_cases h : s < 4640
  · exact SourceCoverChecks200000G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 4384 7 64296 := by
  have suffix : Floor 5760 7 64296 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor006
  intro s hs hbig
  by_cases h : s < 5760
  · exact join004_02 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 4288 7 60652 := by
  have suffix : Floor 4384 7 60652 :=
    weaken (by decide) (by decide) floor004
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 4480 6 35244 := by
  have suffix : Floor 4704 6 35244 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor001
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks200000G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 4384 6 35000 := by
  have suffix : Floor 4480 6 35000 :=
    weaken (by decide) (by decide) floor002
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks200000G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 4288 6 33540 := by
  have suffix : Floor 4384 6 33540 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 4384
  · exact SourceCoverChecks200000G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors200000
