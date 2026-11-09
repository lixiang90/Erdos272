module

public import Erdos272.Arithmetic.N233811.SourceCoverChecks233811G00
public import Erdos272.Arithmetic.N233811.SourceCoverChecks233811G01
public import Erdos272.Arithmetic.N233811.SourceCoverChecks233811G02
public import Erdos272.Arithmetic.N243614.SourceFloors243614

@[expose] public section

namespace JSP233.SourceFloors233811
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join005_00 : ∀ s, 1470 ≤ s → s < 2517 → 35710 ≤ physicalK s 9 :=
  append_cover SourceCoverChecks233811G00.bound0005 SourceCoverChecks233811G00.bound0006
#print axioms join005_00

theorem join005_01 : ∀ s, 2517 ≤ s → s < 4591 → 35710 ≤ physicalK s 9 :=
  append_cover SourceCoverChecks233811G00.bound0007 SourceCoverChecks233811G00.bound0008
#print axioms join005_01

theorem join005_02 : ∀ s, 1470 ≤ s → s < 4591 → 35710 ≤ physicalK s 9 :=
  append_cover join005_00 join005_01
#print axioms join005_02

theorem join005_03 : ∀ s, 1470 ≤ s → s < 4640 → 35710 ≤ physicalK s 9 :=
  append_cover join005_02 SourceCoverChecks233811G00.bound0009
#print axioms join005_03

theorem join008_00 : ∀ s, 4640 ≤ s → s < 5248 → 135832 ≤ physicalK s 10 :=
  append_cover SourceCoverChecks233811G00.bound0012 SourceCoverChecks233811G00.bound0013
#print axioms join008_00

theorem join010_00 : ∀ s, 4704 ≤ s → s < 5152 → 172038 ≤ physicalK s 11 :=
  append_cover SourceCoverChecks233811G00.bound0015 SourceCoverChecks233811G00.bound0016
#print axioms join010_00

theorem floor083 : Floor 147 88 218966 := by
  have suffix : Floor 153 88 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor167
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks233811G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 145 88 215106 := by
  have suffix : Floor 147 88 215106 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks233811G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 145 82 189720 := by
  have suffix : Floor 156 82 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor161
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks233811G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 147 76 172038 := by
  have suffix : Floor 161 76 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor513
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks233811G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 145 74 161862 := by
  have suffix : Floor 158 74 161862 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor155
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks233811G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 205 67 218966 := by
  have suffix : Floor 214 67 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor151
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks233811G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 203 67 215106 := by
  have suffix : Floor 205 67 215106 :=
    weaken (by decide) (by decide) floor078
  intro s hs hbig
  by_cases h : s < 205
  · exact SourceCoverChecks233811G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 145 66 135832 := by
  have suffix : Floor 164 66 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor482
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks233811G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 203 62 189720 := by
  have suffix : Floor 218 62 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor146
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks233811G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 205 58 172038 := by
  have suffix : Floor 224 58 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor438
  intro s hs hbig
  by_cases h : s < 224
  · exact SourceCoverChecks233811G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 203 57 161862 := by
  have suffix : Floor 216 57 161862 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor437
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks233811G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 147 56 106622 := by
  have suffix : Floor 175 56 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor407
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks233811G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 145 56 103932 := by
  have suffix : Floor 147 56 103932 :=
    weaken (by decide) (by decide) floor072
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks233811G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 294 53 218966 := by
  have suffix : Floor 296 53 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor029
  intro s hs hbig
  by_cases h : s < 296
  · exact SourceCoverChecks233811G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 290 53 215106 := by
  have suffix : Floor 290 53 215106 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor428
  exact suffix
#print axioms floor069

theorem floor068 : Floor 203 52 135832 := by
  have suffix : Floor 203 52 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor418
  exact suffix
#print axioms floor068

theorem floor067 : Floor 290 50 189720 := by
  have suffix : Floor 312 50 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor126
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks233811G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 294 47 172038 := by
  have suffix : Floor 296 47 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor028
  intro s hs hbig
  by_cases h : s < 296
  · exact SourceCoverChecks233811G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 290 45 161862 := by
  have suffix : Floor 302 45 161862 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor371
  intro s hs hbig
  by_cases h : s < 302
  · exact SourceCoverChecks233811G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 205 45 106622 := by
  have suffix : Floor 207 45 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor027
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks233811G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 203 44 103932 := by
  have suffix : Floor 232 44 103932 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor337
  intro s hs hbig
  by_cases h : s < 232
  · exact SourceCoverChecks233811G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 147 44 70290 := by
  have suffix : Floor 189 44 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor329
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks233811G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 145 44 69528 := by
  have suffix : Floor 147 44 69528 :=
    weaken (by decide) (by decide) floor062
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks233811G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 441 42 218966 := by
  have suffix : Floor 459 42 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor107
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks233811G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 435 42 215106 := by
  have suffix : Floor 441 42 215106 :=
    weaken (by decide) (by decide) floor060
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks233811G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 290 41 135832 := by
  have suffix : Floor 328 41 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor339
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks233811G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 435 39 189720 := by
  have suffix : Floor 464 39 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor314
  intro s hs hbig
  by_cases h : s < 464
  · exact SourceCoverChecks233811G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 441 37 172038 := by
  have suffix : Floor 448 37 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor303
  intro s hs hbig
  by_cases h : s < 448
  · exact SourceCoverChecks233811G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 435 36 161862 := by
  have suffix : Floor 474 36 161862 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor094
  intro s hs hbig
  by_cases h : s < 474
  · exact SourceCoverChecks233811G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 294 36 106622 := by
  have suffix : Floor 324 36 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor270
  intro s hs hbig
  by_cases h : s < 324
  · exact SourceCoverChecks233811G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 290 36 103932 := by
  have suffix : Floor 294 36 103932 :=
    weaken (by decide) (by decide) floor054
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks233811G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 205 36 70290 := by
  have suffix : Floor 207 36 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor292
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks233811G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 203 36 69528 := by
  have suffix : Floor 203 36 69528 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor291
  exact suffix
#print axioms floor051

theorem floor050 : Floor 435 33 135832 := by
  have suffix : Floor 492 33 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor259
  intro s hs hbig
  by_cases h : s < 492
  · exact SourceCoverChecks233811G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 735 32 218966 := by
  have suffix : Floor 740 32 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor021
  intro s hs hbig
  by_cases h : s < 740
  · exact SourceCoverChecks233811G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 725 32 215106 := by
  have suffix : Floor 735 32 215106 :=
    weaken (by decide) (by decide) floor049
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks233811G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 725 30 189720 := by
  have suffix : Floor 780 30 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor069
  intro s hs hbig
  by_cases h : s < 780
  · exact SourceCoverChecks233811G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 147 30 35710 := by
  have suffix : Floor 207 30 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor016
  intro s hs hbig
  by_cases h : s < 207
  · exact SourceCoverChecks233811G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 145 30 35004 := by
  have suffix : Floor 147 30 35004 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks233811G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 441 29 106622 := by
  have suffix : Floor 444 29 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor017
  intro s hs hbig
  by_cases h : s < 444
  · exact SourceCoverChecks233811G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 435 29 103932 := by
  have suffix : Floor 441 29 103932 :=
    weaken (by decide) (by decide) floor044
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks233811G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 294 29 70290 := by
  have suffix : Floor 378 29 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor197
  intro s hs hbig
  by_cases h : s < 378
  · exact SourceCoverChecks233811G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 290 29 69528 := by
  have suffix : Floor 294 29 69528 :=
    weaken (by decide) (by decide) floor042
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks233811G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 735 28 172038 := by
  have suffix : Floor 805 28 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor201
  intro s hs hbig
  by_cases h : s < 805
  · exact SourceCoverChecks233811G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 725 28 161862 := by
  have suffix : Floor 735 28 161862 :=
    weaken (by decide) (by decide) floor040
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks233811G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 725 25 135832 := by
  have suffix : Floor 820 25 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor174
  intro s hs hbig
  by_cases h : s < 820
  · exact SourceCoverChecks233811G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 205 25 35710 := by
  have suffix : Floor 296 25 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor012
  intro s hs hbig
  by_cases h : s < 296
  · exact SourceCoverChecks233811G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 203 25 35004 := by
  have suffix : Floor 205 25 35004 :=
    weaken (by decide) (by decide) floor037
  intro s hs hbig
  by_cases h : s < 205
  · exact SourceCoverChecks233811G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 441 24 70290 := by
  have suffix : Floor 444 24 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor015
  intro s hs hbig
  by_cases h : s < 444
  · exact SourceCoverChecks233811G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 435 24 69528 := by
  have suffix : Floor 441 24 69528 :=
    weaken (by decide) (by decide) floor035
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks233811G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 1470 23 218966 := by
  have suffix : Floor 1480 23 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor014
  intro s hs hbig
  by_cases h : s < 1480
  · exact SourceCoverChecks233811G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 1450 23 215106 := by
  have suffix : Floor 1470 23 215106 :=
    weaken (by decide) (by decide) floor033
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks233811G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 735 22 106622 := by
  have suffix : Floor 875 22 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor131
  intro s hs hbig
  by_cases h : s < 875
  · exact SourceCoverChecks233811G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 725 22 103932 := by
  have suffix : Floor 735 22 103932 :=
    weaken (by decide) (by decide) floor031
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks233811G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 1450 21 189720 := by
  have suffix : Floor 1560 21 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor042
  intro s hs hbig
  by_cases h : s < 1560
  · exact SourceCoverChecks233811G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 294 21 35710 := by
  have suffix : Floor 296 21 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor012
  intro s hs hbig
  by_cases h : s < 296
  · exact SourceCoverChecks233811G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 290 21 35004 := by
  have suffix : Floor 294 21 35004 :=
    weaken (by decide) (by decide) floor028
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks233811G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 1470 20 172038 := by
  have suffix : Floor 1480 20 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor011
  intro s hs hbig
  by_cases h : s < 1480
  · exact SourceCoverChecks233811G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 1450 20 161862 := by
  have suffix : Floor 1470 20 161862 :=
    weaken (by decide) (by decide) floor026
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks233811G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 1450 18 135832 := by
  have suffix : Floor 1640 18 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor106
  intro s hs hbig
  by_cases h : s < 1640
  · exact SourceCoverChecks233811G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 735 18 70290 := by
  have suffix : Floor 740 18 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor010
  intro s hs hbig
  by_cases h : s < 740
  · exact SourceCoverChecks233811G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 725 18 69528 := by
  have suffix : Floor 735 18 69528 :=
    weaken (by decide) (by decide) floor023
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks233811G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 441 17 35710 := by
  have suffix : Floor 444 17 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor009
  intro s hs hbig
  by_cases h : s < 444
  · exact SourceCoverChecks233811G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 435 17 35004 := by
  have suffix : Floor 441 17 35004 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 441
  · exact SourceCoverChecks233811G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 1470 16 106622 := by
  have suffix : Floor 1480 16 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor008
  intro s hs hbig
  by_cases h : s < 1480
  · exact SourceCoverChecks233811G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 1450 16 103932 := by
  have suffix : Floor 1470 16 103932 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks233811G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 4704 13 218966 := by
  have suffix : Floor 4736 13 218966 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor007
  intro s hs hbig
  by_cases h : s < 4736
  · exact SourceCoverChecks233811G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 4640 13 215106 := by
  have suffix : Floor 4704 13 215106 :=
    weaken (by decide) (by decide) floor017
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks233811G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 1470 13 70290 := by
  have suffix : Floor 1480 13 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor006
  intro s hs hbig
  by_cases h : s < 1480
  · exact SourceCoverChecks233811G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 1450 13 69528 := by
  have suffix : Floor 1470 13 69528 :=
    weaken (by decide) (by decide) floor015
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks233811G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 735 13 35710 := by
  have suffix : Floor 740 13 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor005
  intro s hs hbig
  by_cases h : s < 740
  · exact SourceCoverChecks233811G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 725 13 35004 := by
  have suffix : Floor 735 13 35004 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 735
  · exact SourceCoverChecks233811G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 4640 12 189720 := by
  have suffix : Floor 4800 12 189720 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor015
  intro s hs hbig
  by_cases h : s < 4800
  · exact SourceCoverChecks233811G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 4704 11 172038 := by
  have suffix : Floor 5152 11 172038 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor033
  intro s hs hbig
  by_cases h : s < 5152
  · exact join010_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 4640 11 161862 := by
  have suffix : Floor 4704 11 161862 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks233811G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 4640 10 135832 := by
  have suffix : Floor 5248 10 135832 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor021
  intro s hs hbig
  by_cases h : s < 5248
  · exact join008_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 4704 9 106622 := by
  have suffix : Floor 4736 9 106622 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor002
  intro s hs hbig
  by_cases h : s < 4736
  · exact SourceCoverChecks233811G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 4640 9 103932 := by
  have suffix : Floor 4704 9 103932 :=
    weaken (by decide) (by decide) floor007
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks233811G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 1470 9 35710 := by
  have suffix : Floor 4640 9 35710 :=
    weaken (by decide) (by decide) floor006
  intro s hs hbig
  by_cases h : s < 4640
  · exact join005_03 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 1450 9 35004 := by
  have suffix : Floor 1470 9 35004 :=
    weaken (by decide) (by decide) floor005
  intro s hs hbig
  by_cases h : s < 1470
  · exact SourceCoverChecks233811G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 4704 8 70290 := by
  have suffix : Floor 4736 8 70290 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor001
  intro s hs hbig
  by_cases h : s < 4736
  · exact SourceCoverChecks233811G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 4640 8 69528 := by
  have suffix : Floor 4704 8 69528 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks233811G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 4704 6 35710 := by
  have suffix : Floor 4736 6 35710 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor000
  intro s hs hbig
  by_cases h : s < 4736
  · exact SourceCoverChecks233811G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 4640 6 35004 := by
  have suffix : Floor 4704 6 35004 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 4704
  · exact SourceCoverChecks233811G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors233811
