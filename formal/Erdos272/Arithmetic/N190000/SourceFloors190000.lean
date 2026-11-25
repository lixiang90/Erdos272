module

public import Erdos272.Arithmetic.N190000.SourceCoverChecks190000G00
public import Erdos272.Arithmetic.N190000.SourceCoverChecks190000G01
public import Erdos272.Arithmetic.N190000.SourceCoverChecks190000G02
public import Erdos272.Arithmetic.N200000.SourceFloors200000

@[expose] public section

namespace JSP233.SourceFloors190000
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floor097 : Floor 132 81 165074 := by
  have suffix : Floor 137 81 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor139
  intro s hs hbig
  by_cases h : s < 137
  · exact SourceCoverChecks190000G02.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 130 81 162062 := by
  have suffix : Floor 132 81 162062 :=
    weaken (by decide) (by decide) floor097
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G02.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 132 77 151634 := by
  have suffix : Floor 140 77 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor137
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks190000G02.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 130 77 148642 := by
  have suffix : Floor 132 77 148642 :=
    weaken (by decide) (by decide) floor095
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G02.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 132 71 132580 := by
  have suffix : Floor 145 71 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor076
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks190000G02.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 130 71 130036 := by
  have suffix : Floor 132 71 130036 :=
    weaken (by decide) (by decide) floor093
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G02.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 132 65 115916 := by
  have suffix : Floor 150 65 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor142
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks190000G02.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 130 65 112894 := by
  have suffix : Floor 132 65 112894 :=
    weaken (by decide) (by decide) floor091
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G02.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 184 62 165074 := by
  have suffix : Floor 191 62 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor127
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks190000G02.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 182 61 162062 := by
  have suffix : Floor 191 61 162062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor127
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks190000G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 184 59 151634 := by
  have suffix : Floor 196 59 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor123
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks190000G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 182 58 148642 := by
  have suffix : Floor 196 58 148642 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor123
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks190000G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 132 57 93632 := by
  have suffix : Floor 134 57 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor122
  intro s hs hbig
  by_cases h : s < 134
  · exact SourceCoverChecks190000G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 130 57 92096 := by
  have suffix : Floor 132 57 92096 :=
    weaken (by decide) (by decide) floor085
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 184 54 132580 := by
  have suffix : Floor 198 54 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor418
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks190000G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 182 54 130036 := by
  have suffix : Floor 184 54 130036 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 184
  · exact SourceCoverChecks190000G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 184 51 115916 := by
  have suffix : Floor 210 51 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor122
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks190000G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 182 50 112894 := by
  have suffix : Floor 210 50 112894 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor122
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks190000G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 264 49 165074 := by
  have suffix : Floor 274 49 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor112
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks190000G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 260 49 162062 := by
  have suffix : Floor 264 49 162062 :=
    weaken (by decide) (by decide) floor079
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 264 46 151634 := by
  have suffix : Floor 280 46 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor109
  intro s hs hbig
  by_cases h : s < 280
  · exact SourceCoverChecks190000G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 260 46 148642 := by
  have suffix : Floor 264 46 148642 :=
    weaken (by decide) (by decide) floor077
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 132 46 64960 := by
  have suffix : Floor 140 46 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor105
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks190000G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 184 45 93632 := by
  have suffix : Floor 187 45 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor106
  intro s hs hbig
  by_cases h : s < 187
  · exact SourceCoverChecks190000G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 182 45 92096 := by
  have suffix : Floor 184 45 92096 :=
    weaken (by decide) (by decide) floor074
  intro s hs hbig
  by_cases h : s < 184
  · exact SourceCoverChecks190000G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 130 45 62912 := by
  have suffix : Floor 137 45 62912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor103
  intro s hs hbig
  by_cases h : s < 137
  · exact SourceCoverChecks190000G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 264 43 132580 := by
  have suffix : Floor 277 43 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor348
  intro s hs hbig
  by_cases h : s < 277
  · exact SourceCoverChecks190000G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 260 43 130036 := by
  have suffix : Floor 264 43 130036 :=
    weaken (by decide) (by decide) floor071
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 264 40 115916 := by
  have suffix : Floor 300 40 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor099
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks190000G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 260 40 112894 := by
  have suffix : Floor 264 40 112894 :=
    weaken (by decide) (by decide) floor069
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 396 39 165074 := by
  have suffix : Floor 402 39 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor095
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks190000G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 390 38 162062 := by
  have suffix : Floor 411 38 162062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor094
  intro s hs hbig
  by_cases h : s < 411
  · exact SourceCoverChecks190000G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 396 37 151634 := by
  have suffix : Floor 414 37 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor293
  intro s hs hbig
  by_cases h : s < 414
  · exact SourceCoverChecks190000G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 390 37 148642 := by
  have suffix : Floor 396 37 148642 :=
    weaken (by decide) (by decide) floor065
  intro s hs hbig
  by_cases h : s < 396
  · exact SourceCoverChecks190000G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 184 37 64960 := by
  have suffix : Floor 184 37 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor299
  exact suffix
#print axioms floor063

theorem floor062 : Floor 264 36 93632 := by
  have suffix : Floor 268 36 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor087
  intro s hs hbig
  by_cases h : s < 268
  · exact SourceCoverChecks190000G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 260 36 92096 := by
  have suffix : Floor 264 36 92096 :=
    weaken (by decide) (by decide) floor062
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 182 36 62912 := by
  have suffix : Floor 191 36 62912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor086
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks190000G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 396 35 132580 := by
  have suffix : Floor 396 35 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor283
  exact suffix
#print axioms floor059

theorem floor058 : Floor 390 34 130036 := by
  have suffix : Floor 420 34 130036 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor083
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks190000G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 396 32 115916 := by
  have suffix : Floor 450 32 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor070
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks190000G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 390 32 112894 := by
  have suffix : Floor 396 32 112894 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 396
  · exact SourceCoverChecks190000G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 132 31 33422 := by
  have suffix : Floor 134 31 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor077
  intro s hs hbig
  by_cases h : s < 134
  · exact SourceCoverChecks190000G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 130 31 32175 := by
  have suffix : Floor 132 31 32175 :=
    weaken (by decide) (by decide) floor055
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 264 30 64960 := by
  have suffix : Floor 277 30 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor230
  intro s hs hbig
  by_cases h : s < 277
  · exact SourceCoverChecks190000G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 660 29 165074 := by
  have suffix : Floor 685 29 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor071
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks190000G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 650 29 162062 := by
  have suffix : Floor 660 29 162062 :=
    weaken (by decide) (by decide) floor052
  intro s hs hbig
  by_cases h : s < 660
  · exact SourceCoverChecks190000G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 396 29 93632 := by
  have suffix : Floor 402 29 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor069
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks190000G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 390 29 92096 := by
  have suffix : Floor 396 29 92096 :=
    weaken (by decide) (by decide) floor050
  intro s hs hbig
  by_cases h : s < 396
  · exact SourceCoverChecks190000G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 260 29 62912 := by
  have suffix : Floor 274 29 62912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor068
  intro s hs hbig
  by_cases h : s < 274
  · exact SourceCoverChecks190000G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 660 28 151634 := by
  have suffix : Floor 700 28 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor066
  intro s hs hbig
  by_cases h : s < 700
  · exact SourceCoverChecks190000G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 650 28 148642 := by
  have suffix : Floor 660 28 148642 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 660
  · exact SourceCoverChecks190000G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 660 26 132580 := by
  have suffix : Floor 725 26 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor038
  intro s hs hbig
  by_cases h : s < 725
  · exact SourceCoverChecks190000G01.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 650 26 130036 := by
  have suffix : Floor 660 26 130036 :=
    weaken (by decide) (by decide) floor045
  intro s hs hbig
  by_cases h : s < 660
  · exact SourceCoverChecks190000G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 184 26 33422 := by
  have suffix : Floor 187 26 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor061
  intro s hs hbig
  by_cases h : s < 187
  · exact SourceCoverChecks190000G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 660 25 115916 := by
  have suffix : Floor 670 25 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor058
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks190000G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 182 25 32175 := by
  have suffix : Floor 203 25 32175 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor036
  intro s hs hbig
  by_cases h : s < 203
  · exact SourceCoverChecks190000G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 650 24 112894 := by
  have suffix : Floor 750 24 112894 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor050
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks190000G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 396 24 64960 := by
  have suffix : Floor 420 24 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor057
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks190000G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 390 24 62912 := by
  have suffix : Floor 396 24 62912 :=
    weaken (by decide) (by decide) floor039
  intro s hs hbig
  by_cases h : s < 396
  · exact SourceCoverChecks190000G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 660 22 93632 := by
  have suffix : Floor 670 22 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor050
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks190000G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 650 22 92096 := by
  have suffix : Floor 660 22 92096 :=
    weaken (by decide) (by decide) floor037
  intro s hs hbig
  by_cases h : s < 660
  · exact SourceCoverChecks190000G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 1320 21 165074 := by
  have suffix : Floor 1340 21 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor048
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 1300 21 162062 := by
  have suffix : Floor 1320 21 162062 :=
    weaken (by decide) (by decide) floor035
  intro s hs hbig
  by_cases h : s < 1320
  · exact SourceCoverChecks190000G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 264 21 33422 := by
  have suffix : Floor 268 21 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor045
  intro s hs hbig
  by_cases h : s < 268
  · exact SourceCoverChecks190000G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 260 21 32175 := by
  have suffix : Floor 264 21 32175 :=
    weaken (by decide) (by decide) floor033
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks190000G01.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 1320 20 151634 := by
  have suffix : Floor 1340 20 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor044
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 1300 20 148642 := by
  have suffix : Floor 1320 20 148642 :=
    weaken (by decide) (by decide) floor031
  intro s hs hbig
  by_cases h : s < 1320
  · exact SourceCoverChecks190000G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 1320 19 132580 := by
  have suffix : Floor 1340 19 132580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor042
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 1300 19 130036 := by
  have suffix : Floor 1320 19 130036 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 1320
  · exact SourceCoverChecks190000G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 660 19 64960 := by
  have suffix : Floor 700 19 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor041
  intro s hs hbig
  by_cases h : s < 700
  · exact SourceCoverChecks190000G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 1320 18 115916 := by
  have suffix : Floor 1340 18 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor038
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 650 18 62912 := by
  have suffix : Floor 685 18 62912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor037
  intro s hs hbig
  by_cases h : s < 685
  · exact SourceCoverChecks190000G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 1300 17 112894 := by
  have suffix : Floor 1500 17 112894 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor028
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks190000G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 396 17 33422 := by
  have suffix : Floor 402 17 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor033
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks190000G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 390 17 32175 := by
  have suffix : Floor 396 17 32175 :=
    weaken (by decide) (by decide) floor023
  intro s hs hbig
  by_cases h : s < 396
  · exact SourceCoverChecks190000G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 1320 16 93632 := by
  have suffix : Floor 1340 16 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor030
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 1300 16 92096 := by
  have suffix : Floor 1320 16 92096 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 1320
  · exact SourceCoverChecks190000G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 1320 13 64960 := by
  have suffix : Floor 1400 13 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor029
  intro s hs hbig
  by_cases h : s < 1400
  · exact SourceCoverChecks190000G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 1300 13 62912 := by
  have suffix : Floor 1320 13 62912 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 1320
  · exact SourceCoverChecks190000G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 660 13 33422 := by
  have suffix : Floor 670 13 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor024
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks190000G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 650 13 32175 := by
  have suffix : Floor 660 13 32175 :=
    weaken (by decide) (by decide) floor017
  intro s hs hbig
  by_cases h : s < 660
  · exact SourceCoverChecks190000G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 4224 12 165074 := by
  have suffix : Floor 4288 12 165074 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor021
  intro s hs hbig
  by_cases h : s < 4288
  · exact SourceCoverChecks190000G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 4160 12 162062 := by
  have suffix : Floor 4224 12 162062 :=
    weaken (by decide) (by decide) floor015
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 4224 11 151634 := by
  have suffix : Floor 4480 11 151634 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor020
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks190000G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 4160 11 148642 := by
  have suffix : Floor 4224 11 148642 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 4224 10 115916 := by
  have suffix : Floor 4288 10 115916 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor015
  intro s hs hbig
  by_cases h : s < 4288
  · exact SourceCoverChecks190000G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 4160 10 112894 := by
  have suffix : Floor 4224 10 112894 :=
    weaken (by decide) (by decide) floor011
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 1300 10 32175 := by
  have suffix : Floor 1340 10 32175 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor007
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 132 10 3786 :=
  of_prefix_tail (C := 492) (by decide) (by decide) (by decide +kernel) SourceCoverChecks190000G00.bound0008
#print axioms floor008

theorem floor007 : Floor 130 10 3661 := by
  have suffix : Floor 132 10 3661 :=
    weaken (by decide) (by decide) floor008
  intro s hs hbig
  by_cases h : s < 132
  · exact SourceCoverChecks190000G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 4224 9 93632 := by
  have suffix : Floor 4288 9 93632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor009
  intro s hs hbig
  by_cases h : s < 4288
  · exact SourceCoverChecks190000G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 4160 9 92096 := by
  have suffix : Floor 4224 9 92096 :=
    weaken (by decide) (by decide) floor006
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 1320 9 33422 := by
  have suffix : Floor 1340 9 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor007
  intro s hs hbig
  by_cases h : s < 1340
  · exact SourceCoverChecks190000G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 4224 8 64960 := by
  have suffix : Floor 4480 8 64960 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor005
  intro s hs hbig
  by_cases h : s < 4480
  · exact SourceCoverChecks190000G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 4160 8 62912 := by
  have suffix : Floor 4224 8 62912 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 4224 6 33422 := by
  have suffix : Floor 4288 6 33422 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor000
  intro s hs hbig
  by_cases h : s < 4288
  · exact SourceCoverChecks190000G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 4160 6 32175 := by
  have suffix : Floor 4224 6 32175 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 4224
  · exact SourceCoverChecks190000G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors190000
