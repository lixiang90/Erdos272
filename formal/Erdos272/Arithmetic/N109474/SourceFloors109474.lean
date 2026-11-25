module

public import Erdos272.Arithmetic.N109474.SourceCoverChecks109474G00
public import Erdos272.Arithmetic.N109474.SourceCoverChecks109474G01
public import Erdos272.Arithmetic.N109474.SourceCoverChecks109474G02
public import Erdos272.Arithmetic.N118533.SourceFloors118533

@[expose] public section

namespace JSP233.SourceFloors109474
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floor145 : Floor 111 66 92726 := by
  have suffix : Floor 114 66 92726 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor186
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks109474G02.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 109 66 91072 := by
  have suffix : Floor 111 66 91072 :=
    weaken (by decide) (by decide) floor145
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks109474G02.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 110 65 89390 := by
  have suffix : Floor 114 65 89390 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor186
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks109474G02.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 113 64 88700 := by
  have suffix : Floor 114 64 88700 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor183
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks109474G02.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 111 64 87678 := by
  have suffix : Floor 113 64 87678 :=
    weaken (by decide) (by decide) floor142
  intro s hs hbig
  by_cases h : s < 113
  · exact SourceCoverChecks109474G02.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 113 62 85106 := by
  have suffix : Floor 115 62 85106 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor182
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks109474G02.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 112 61 82230 := by
  have suffix : Floor 114 61 82230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor181
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks109474G02.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 113 60 81502 := by
  have suffix : Floor 115 60 81502 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor180
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks109474G02.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 116 59 81120 := by
  have suffix : Floor 117 59 81120 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor055
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G02.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 114 59 78476 := by
  have suffix : Floor 116 59 78476 :=
    weaken (by decide) (by decide) floor137
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks109474G02.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 115 58 78320 := by
  have suffix : Floor 117 58 78320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor061
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G02.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 115 56 74808 := by
  have suffix : Floor 117 56 74808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor016
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G02.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 146 55 102588 := by
  have suffix : Floor 156 55 102588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor050
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G02.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 116 55 73870 := by
  have suffix : Floor 119 55 73870 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor052
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks109474G02.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 114 55 72108 := by
  have suffix : Floor 116 55 72108 :=
    weaken (by decide) (by decide) floor132
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks109474G02.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 118 53 71058 := by
  have suffix : Floor 124 53 71058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor106
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks109474G02.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 116 53 68396 := by
  have suffix : Floor 117 53 68396 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor015
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G02.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 153 52 95702 := by
  have suffix : Floor 156 52 95702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor049
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G02.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 151 51 92726 := by
  have suffix : Floor 156 51 92726 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor049
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G01.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 150 51 91072 := by
  have suffix : Floor 151 51 91072 :=
    weaken (by decide) (by decide) floor127
  intro s hs hbig
  by_cases h : s < 151
  · exact SourceCoverChecks109474G01.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 116 51 64982 := by
  have suffix : Floor 119 51 64982 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor046
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks109474G01.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 150 50 89390 := by
  have suffix : Floor 156 50 89390 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor046
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G01.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 146 50 86189 := by
  have suffix : Floor 150 50 86189 :=
    weaken (by decide) (by decide) floor124
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks109474G01.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 153 49 87906 := by
  have suffix : Floor 156 49 87906 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor046
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G01.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 150 49 85822 := by
  have suffix : Floor 153 49 85822 :=
    weaken (by decide) (by decide) floor122
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks109474G01.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 116 49 62162 := by
  have suffix : Floor 117 49 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor055
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G01.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 153 48 84302 := by
  have suffix : Floor 156 48 84302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor120
  intro s hs hbig
  by_cases h : s < 156
  · exact SourceCoverChecks109474G01.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 150 48 82230 := by
  have suffix : Floor 153 48 82230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor119
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks109474G01.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 116 47 57892 := by
  have suffix : Floor 120 47 57892 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor045
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks109474G01.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 151 46 78320 := by
  have suffix : Floor 161 46 78320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor157
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks109474G01.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 117 46 56770 := by
  have suffix : Floor 127 46 56770 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor083
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks109474G01.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 118 45 55024 := by
  have suffix : Floor 120 45 55024 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor095
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks109474G01.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 116 45 54134 := by
  have suffix : Floor 118 45 54134 :=
    weaken (by decide) (by decide) floor114
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks109474G01.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 116 43 49886 := by
  have suffix : Floor 120 43 49886 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor040
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks109474G01.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 117 42 48338 := by
  have suffix : Floor 130 42 48338 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor039
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks109474G01.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 227 41 102588 := by
  have suffix : Floor 228 41 102588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor142
  intro s hs hbig
  by_cases h : s < 228
  · exact SourceCoverChecks109474G01.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 178 41 77234 := by
  have suffix : Floor 189 41 77234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor116
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks109474G01.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 175 41 75294 := by
  have suffix : Floor 178 41 75294 :=
    weaken (by decide) (by decide) floor109
  intro s hs hbig
  by_cases h : s < 178
  · exact SourceCoverChecks109474G01.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 166 41 72108 := by
  have suffix : Floor 173 41 72108 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor090
  intro s hs hbig
  by_cases h : s < 173
  · exact SourceCoverChecks109474G01.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 118 41 47576 := by
  have suffix : Floor 130 41 47576 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor039
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks109474G01.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 116 41 45906 := by
  have suffix : Floor 118 41 45906 :=
    weaken (by decide) (by decide) floor106
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks109474G01.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 100 41 36560 := by
  have suffix : Floor 108 41 36560 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor111
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks109474G01.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 178 40 73870 := by
  have suffix : Floor 180 40 73870 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor080
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks109474G01.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 146 40 57962 := by
  have suffix : Floor 161 40 57962 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor136
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks109474G01.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 176 39 70292 := by
  have suffix : Floor 189 39 70292 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor112
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks109474G01.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 175 39 68396 := by
  have suffix : Floor 176 39 68396 :=
    weaken (by decide) (by decide) floor101
  intro s hs hbig
  by_cases h : s < 176
  · exact SourceCoverChecks109474G01.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 118 39 42620 := by
  have suffix : Floor 150 39 42620 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor084
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks109474G01.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 116 39 41472 := by
  have suffix : Floor 118 39 41472 :=
    weaken (by decide) (by decide) floor099
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks109474G01.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 175 38 64982 := by
  have suffix : Floor 180 38 64982 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor312
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks109474G01.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 115 38 38970 := by
  have suffix : Floor 130 38 38970 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor102
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks109474G01.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 191 37 69838 := by
  have suffix : Floor 196 37 69838 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor109
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks109474G01.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 178 37 63368 := by
  have suffix : Floor 184 37 63368 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor063
  intro s hs hbig
  by_cases h : s < 184
  · exact SourceCoverChecks109474G01.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 176 37 62162 := by
  have suffix : Floor 178 37 62162 :=
    weaken (by decide) (by decide) floor094
  intro s hs hbig
  by_cases h : s < 178
  · exact SourceCoverChecks109474G01.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 175 37 61460 := by
  have suffix : Floor 176 37 61460 :=
    weaken (by decide) (by decide) floor093
  intro s hs hbig
  by_cases h : s < 176
  · exact SourceCoverChecks109474G01.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 118 37 39466 := by
  have suffix : Floor 130 37 39466 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor102
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks109474G01.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 175 36 57892 := by
  have suffix : Floor 177 36 57892 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor071
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks109474G01.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 117 36 37698 := by
  have suffix : Floor 124 36 37698 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor079
  intro s hs hbig
  by_cases h : s < 124
  · exact SourceCoverChecks109474G01.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 260 35 86189 := by
  have suffix : Floor 312 35 86189 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor033
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks109474G01.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 176 35 56770 := by
  have suffix : Floor 177 35 56770 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor071
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks109474G01.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 178 34 55024 := by
  have suffix : Floor 189 34 55024 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor099
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks109474G01.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 116 34 33220 := by
  have suffix : Floor 117 34 33220 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor040
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks109474G01.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 306 33 95702 := by
  have suffix : Floor 312 33 95702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor030
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks109474G01.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 303 33 92726 := by
  have suffix : Floor 306 33 92726 :=
    weaken (by decide) (by decide) floor084
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks109474G01.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 300 33 91072 := by
  have suffix : Floor 303 33 91072 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 303
  · exact SourceCoverChecks109474G01.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 175 33 49886 := by
  have suffix : Floor 182 33 49886 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor029
  intro s hs hbig
  by_cases h : s < 182
  · exact SourceCoverChecks109474G01.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 118 33 32593 := by
  have suffix : Floor 127 33 32593 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor064
  intro s hs hbig
  by_cases h : s < 127
  · exact SourceCoverChecks109474G01.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 306 32 87906 := by
  have suffix : Floor 312 32 87906 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor028
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks109474G01.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 300 32 87678 := by
  have suffix : Floor 306 32 87678 :=
    weaken (by decide) (by decide) floor079
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks109474G01.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 176 32 48338 := by
  have suffix : Floor 189 32 48338 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor092
  intro s hs hbig
  by_cases h : s < 189
  · exact SourceCoverChecks109474G01.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 175 32 45906 := by
  have suffix : Floor 176 32 45906 :=
    weaken (by decide) (by decide) floor077
  intro s hs hbig
  by_cases h : s < 176
  · exact SourceCoverChecks109474G01.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 306 31 84302 := by
  have suffix : Floor 312 31 84302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor075
  intro s hs hbig
  by_cases h : s < 312
  · exact SourceCoverChecks109474G01.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 300 31 82230 := by
  have suffix : Floor 306 31 82230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor074
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks109474G01.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 116 31 28519 := by
  have suffix : Floor 130 31 28519 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor054
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks109474G01.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 102 31 23353 := by
  have suffix : Floor 104 31 23353 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor027
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks109474G01.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 303 30 78320 := by
  have suffix : Floor 342 30 78320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor110
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks109474G01.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 300 29 72108 := by
  have suffix : Floor 342 29 72108 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor104
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks109474G01.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 260 28 57962 := by
  have suffix : Floor 342 28 57962 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor104
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks109474G01.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 204 28 42620 := by
  have suffix : Floor 208 28 42620 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor025
  intro s hs hbig
  by_cases h : s < 208
  · exact SourceCoverChecks109474G01.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 116 28 22860 := by
  have suffix : Floor 159 28 22860 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor102
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks109474G01.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 202 27 41472 := by
  have suffix : Floor 210 27 41472 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor063
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks109474G01.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 200 27 40533 := by
  have suffix : Floor 202 27 40533 :=
    weaken (by decide) (by decide) floor066
  intro s hs hbig
  by_cases h : s < 202
  · exact SourceCoverChecks109474G01.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 599 24 102588 := by
  have suffix : Floor 600 24 102588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor022
  intro s hs hbig
  by_cases h : s < 600
  · exact SourceCoverChecks109474G01.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 569 24 92448 := by
  have suffix : Floor 570 24 92448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor082
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks109474G00.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 565 24 91072 := by
  have suffix : Floor 569 24 91072 :=
    weaken (by decide) (by decide) floor063
  intro s hs hbig
  by_cases h : s < 569
  · exact SourceCoverChecks109474G00.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 200 24 33220 := by
  have suffix : Floor 214 24 33220 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor019
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks109474G00.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 560 23 89390 := by
  have suffix : Floor 635 23 89390 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor047
  intro s hs hbig
  by_cases h : s < 635
  · exact SourceCoverChecks109474G00.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 558 23 88700 := by
  have suffix : Floor 560 23 88700 :=
    weaken (by decide) (by decide) floor060
  intro s hs hbig
  by_cases h : s < 560
  · exact SourceCoverChecks109474G00.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 555 23 87906 := by
  have suffix : Floor 558 23 87906 :=
    weaken (by decide) (by decide) floor059
  intro s hs hbig
  by_cases h : s < 558
  · exact SourceCoverChecks109474G00.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 550 23 86189 := by
  have suffix : Floor 554 23 86189 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor073
  intro s hs hbig
  by_cases h : s < 554
  · exact SourceCoverChecks109474G00.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 549 23 85822 := by
  have suffix : Floor 550 23 85822 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 550
  · exact SourceCoverChecks109474G00.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 544 23 84302 := by
  have suffix : Floor 545 23 84302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor018
  intro s hs hbig
  by_cases h : s < 545
  · exact SourceCoverChecks109474G00.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 538 23 82230 := by
  have suffix : Floor 540 23 82230 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor071
  intro s hs hbig
  by_cases h : s < 540
  · exact SourceCoverChecks109474G00.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 535 23 81502 := by
  have suffix : Floor 536 23 81502 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor070
  intro s hs hbig
  by_cases h : s < 536
  · exact SourceCoverChecks109474G00.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 534 23 81120 := by
  have suffix : Floor 535 23 81120 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor016
  intro s hs hbig
  by_cases h : s < 535
  · exact SourceCoverChecks109474G00.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 526 23 78476 := by
  have suffix : Floor 527 23 78476 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor069
  intro s hs hbig
  by_cases h : s < 527
  · exact SourceCoverChecks109474G00.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 525 23 78320 := by
  have suffix : Floor 526 23 78320 :=
    weaken (by decide) (by decide) floor051
  intro s hs hbig
  by_cases h : s < 526
  · exact SourceCoverChecks109474G00.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 521 23 77234 := by
  have suffix : Floor 525 23 77234 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor076
  intro s hs hbig
  by_cases h : s < 525
  · exact SourceCoverChecks109474G00.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 515 23 75294 := by
  have suffix : Floor 517 23 75294 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor015
  intro s hs hbig
  by_cases h : s < 517
  · exact SourceCoverChecks109474G00.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 513 23 74808 := by
  have suffix : Floor 515 23 74808 :=
    weaken (by decide) (by decide) floor048
  intro s hs hbig
  by_cases h : s < 515
  · exact SourceCoverChecks109474G00.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 200 23 28519 := by
  have suffix : Floor 216 23 28519 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor067
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks109474G00.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 116 23 16800 := by
  have suffix : Floor 200 23 16800 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks109474G00.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 510 22 73870 := by
  have suffix : Floor 513 22 73870 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor066
  intro s hs hbig
  by_cases h : s < 513
  · exact SourceCoverChecks109474G00.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 504 22 72108 := by
  have suffix : Floor 509 22 72108 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor023
  intro s hs hbig
  by_cases h : s < 509
  · exact SourceCoverChecks109474G00.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 501 22 71058 := by
  have suffix : Floor 504 22 71058 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor072
  intro s hs hbig
  by_cases h : s < 504
  · exact SourceCoverChecks109474G00.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 496 22 69838 := by
  have suffix : Floor 498 22 69838 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor064
  intro s hs hbig
  by_cases h : s < 498
  · exact SourceCoverChecks109474G00.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 491 22 68396 := by
  have suffix : Floor 492 22 68396 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor063
  intro s hs hbig
  by_cases h : s < 492
  · exact SourceCoverChecks109474G00.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 490 22 68008 := by
  have suffix : Floor 491 22 68008 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor013
  intro s hs hbig
  by_cases h : s < 491
  · exact SourceCoverChecks109474G00.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 479 22 64982 := by
  have suffix : Floor 483 22 64982 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor021
  intro s hs hbig
  by_cases h : s < 483
  · exact SourceCoverChecks109474G00.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 473 22 63368 := by
  have suffix : Floor 476 22 63368 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor022
  intro s hs hbig
  by_cases h : s < 476
  · exact SourceCoverChecks109474G00.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 469 21 62162 := by
  have suffix : Floor 472 21 62162 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor060
  intro s hs hbig
  by_cases h : s < 472
  · exact SourceCoverChecks109474G00.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 466 21 61460 := by
  have suffix : Floor 469 21 61460 :=
    weaken (by decide) (by decide) floor036
  intro s hs hbig
  by_cases h : s < 469
  · exact SourceCoverChecks109474G00.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 453 21 57962 := by
  have suffix : Floor 460 21 57962 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor058
  intro s hs hbig
  by_cases h : s < 460
  · exact SourceCoverChecks109474G00.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 449 21 56770 := by
  have suffix : Floor 453 21 56770 :=
    weaken (by decide) (by decide) floor034
  intro s hs hbig
  by_cases h : s < 453
  · exact SourceCoverChecks109474G00.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 442 21 55024 := by
  have suffix : Floor 443 21 55024 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor056
  intro s hs hbig
  by_cases h : s < 443
  · exact SourceCoverChecks109474G00.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 438 21 54134 := by
  have suffix : Floor 442 21 54134 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor019
  intro s hs hbig
  by_cases h : s < 442
  · exact SourceCoverChecks109474G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 421 20 49886 := by
  have suffix : Floor 431 20 49886 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor051
  intro s hs hbig
  by_cases h : s < 431
  · exact SourceCoverChecks109474G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 415 20 48338 := by
  have suffix : Floor 420 20 48338 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor050
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks109474G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 411 20 47576 := by
  have suffix : Floor 412 20 47576 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor008
  intro s hs hbig
  by_cases h : s < 412
  · exact SourceCoverChecks109474G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 404 20 45906 := by
  have suffix : Floor 409 20 45906 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor049
  intro s hs hbig
  by_cases h : s < 409
  · exact SourceCoverChecks109474G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 390 20 42620 := by
  have suffix : Floor 397 20 42620 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor007
  intro s hs hbig
  by_cases h : s < 397
  · exact SourceCoverChecks109474G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 204 20 23353 := by
  have suffix : Floor 208 20 23353 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor006
  intro s hs hbig
  by_cases h : s < 208
  · exact SourceCoverChecks109474G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 202 20 22860 := by
  have suffix : Floor 204 20 22860 :=
    weaken (by decide) (by decide) floor025
  intro s hs hbig
  by_cases h : s < 204
  · exact SourceCoverChecks109474G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 200 20 22373 := by
  have suffix : Floor 202 20 22373 :=
    weaken (by decide) (by decide) floor024
  intro s hs hbig
  by_cases h : s < 202
  · exact SourceCoverChecks109474G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 100 20 10239 := by
  have suffix : Floor 159 20 10239 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor053
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks109474G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 385 19 41472 := by
  have suffix : Floor 389 19 41472 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor047
  intro s hs hbig
  by_cases h : s < 389
  · exact SourceCoverChecks109474G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 376 19 39466 := by
  have suffix : Floor 378 19 39466 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor058
  intro s hs hbig
  by_cases h : s < 378
  · exact SourceCoverChecks109474G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 373 19 38970 := by
  have suffix : Floor 376 19 38970 :=
    weaken (by decide) (by decide) floor020
  intro s hs hbig
  by_cases h : s < 376
  · exact SourceCoverChecks109474G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 368 19 37698 := by
  have suffix : Floor 372 19 37698 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor038
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks109474G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 362 19 36560 := by
  have suffix : Floor 365 19 36560 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor044
  intro s hs hbig
  by_cases h : s < 365
  · exact SourceCoverChecks109474G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 346 18 33220 := by
  have suffix : Floor 347 18 33220 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor004
  intro s hs hbig
  by_cases h : s < 347
  · exact SourceCoverChecks109474G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 342 18 32593 := by
  have suffix : Floor 346 18 32593 :=
    weaken (by decide) (by decide) floor016
  intro s hs hbig
  by_cases h : s < 346
  · exact SourceCoverChecks109474G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 338 18 31697 := by
  have suffix : Floor 340 18 31697 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor056
  intro s hs hbig
  by_cases h : s < 340
  · exact SourceCoverChecks109474G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 321 18 28519 := by
  have suffix : Floor 328 18 28519 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor041
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks109474G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 118 18 10729 := by
  have suffix : Floor 159 18 10729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor053
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks109474G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 117 18 10519 := by
  have suffix : Floor 118 18 10519 :=
    weaken (by decide) (by decide) floor012
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks109474G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 292 17 23353 := by
  have suffix : Floor 298 17 23353 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor003
  intro s hs hbig
  by_cases h : s < 298
  · exact SourceCoverChecks109474G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 289 17 22860 := by
  have suffix : Floor 292 17 22860 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 292
  · exact SourceCoverChecks109474G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 286 17 22373 := by
  have suffix : Floor 289 17 22373 :=
    weaken (by decide) (by decide) floor009
  intro s hs hbig
  by_cases h : s < 289
  · exact SourceCoverChecks109474G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 200 17 16800 := by
  have suffix : Floor 285 17 16800 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor039
  intro s hs hbig
  by_cases h : s < 285
  · exact SourceCoverChecks109474G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 258 15 16800 := by
  have suffix : Floor 570 15 16800 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor042
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks109474G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 195 14 10729 := by
  have suffix : Floor 198 14 10729 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor002
  intro s hs hbig
  by_cases h : s < 198
  · exact SourceCoverChecks109474G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 193 14 10519 := by
  have suffix : Floor 195 14 10519 :=
    weaken (by decide) (by decide) floor005
  intro s hs hbig
  by_cases h : s < 195
  · exact SourceCoverChecks109474G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 190 14 10239 := by
  have suffix : Floor 193 14 10239 :=
    weaken (by decide) (by decide) floor004
  intro s hs hbig
  by_cases h : s < 193
  · exact SourceCoverChecks109474G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 102 10 2869 := by
  have suffix : Floor 104 10 2869 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor000
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks109474G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 101 10 2815 := by
  have suffix : Floor 102 10 2815 :=
    weaken (by decide) (by decide) floor002
  intro s hs hbig
  by_cases h : s < 102
  · exact SourceCoverChecks109474G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 114 9 2761 := by
  have suffix : Floor 134 9 2761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor006
  intro s hs hbig
  by_cases h : s < 134
  · exact SourceCoverChecks109474G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors109474
