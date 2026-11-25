module

public import Erdos272.Arithmetic.N88404.SourceCoverChecks88404G00
public import Erdos272.Arithmetic.N88404.SourceCoverChecks88404G01
public import Erdos272.Arithmetic.N88404.SourceCoverChecks88404G02
public import Erdos272.Arithmetic.N94488.SourceFloors94488

@[expose] public section

namespace JSP233.SourceFloors88404
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floor151 : Floor 102 57 64934 := by
  have suffix : Floor 104 57 64934 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor165
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks88404G02.bound0151 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor151

theorem floor150 : Floor 100 57 62624 := by
  have suffix : Floor 102 57 62624 :=
    weaken (by decide) (by decide) floor151
  intro s hs hbig
  by_cases h : s < 102
  · exact SourceCoverChecks88404G02.bound0150 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor150

theorem floor149 : Floor 101 56 62278 := by
  have suffix : Floor 104 56 62278 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor160
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks88404G02.bound0149 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor149

theorem floor148 : Floor 101 55 60062 := by
  have suffix : Floor 104 55 60062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor160
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks88404G02.bound0148 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor148

theorem floor147 : Floor 103 54 59548 := by
  have suffix : Floor 105 54 59548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor159
  intro s hs hbig
  by_cases h : s < 105
  · exact SourceCoverChecks88404G02.bound0147 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor147

theorem floor146 : Floor 100 54 57856 := by
  have suffix : Floor 103 54 57856 :=
    weaken (by decide) (by decide) floor147
  intro s hs hbig
  by_cases h : s < 103
  · exact SourceCoverChecks88404G02.bound0146 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor146

theorem floor145 : Floor 104 53 59368 := by
  have suffix : Floor 106 53 59368 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor157
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G02.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 102 53 57032 := by
  have suffix : Floor 104 53 57032 :=
    weaken (by decide) (by decide) floor145
  intro s hs hbig
  by_cases h : s < 104
  · exact SourceCoverChecks88404G02.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 103 52 56820 := by
  have suffix : Floor 105 52 56820 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor155
  intro s hs hbig
  by_cases h : s < 105
  · exact SourceCoverChecks88404G02.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 102 52 55630 := by
  have suffix : Floor 103 52 55630 :=
    weaken (by decide) (by decide) floor143
  intro s hs hbig
  by_cases h : s < 103
  · exact SourceCoverChecks88404G02.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 102 51 54238 := by
  have suffix : Floor 106 51 54238 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor152
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G02.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 105 50 54268 := by
  have suffix : Floor 106 50 54268 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor151
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G02.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 102 50 52900 := by
  have suffix : Floor 105 50 52900 :=
    weaken (by decide) (by decide) floor140
  intro s hs hbig
  by_cases h : s < 105
  · exact SourceCoverChecks88404G02.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 104 49 51738 := by
  have suffix : Floor 107 49 51738 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor148
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G02.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 103 48 49794 := by
  have suffix : Floor 107 48 49794 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor148
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G02.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 106 47 50768 := by
  have suffix : Floor 108 47 50768 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor124
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G02.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 105 47 50078 := by
  have suffix : Floor 106 47 50078 :=
    weaken (by decide) (by decide) floor136
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G02.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 104 47 49168 := by
  have suffix : Floor 105 47 49168 :=
    weaken (by decide) (by decide) floor135
  intro s hs hbig
  by_cases h : s < 105
  · exact SourceCoverChecks88404G02.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 103 46 47548 := by
  have suffix : Floor 107 46 47548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor044
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G02.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 102 45 45160 := by
  have suffix : Floor 108 45 45160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor121
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G02.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 138 44 64934 := by
  have suffix : Floor 145 44 64934 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor061
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks88404G02.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 135 44 62624 := by
  have suffix : Floor 137 44 62624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor103
  intro s hs hbig
  by_cases h : s < 137
  · exact SourceCoverChecks88404G02.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 107 44 45830 := by
  have suffix : Floor 108 44 45830 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor121
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G02.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 105 44 44770 := by
  have suffix : Floor 107 44 44770 :=
    weaken (by decide) (by decide) floor129
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G02.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 108 43 44796 := by
  have suffix : Floor 110 43 44796 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor131
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks88404G01.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 106 43 43656 := by
  have suffix : Floor 108 43 43656 :=
    weaken (by decide) (by decide) floor127
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G01.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 135 42 57856 := by
  have suffix : Floor 146 42 57856 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor102
  intro s hs hbig
  by_cases h : s < 146
  · exact SourceCoverChecks88404G01.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 107 42 43024 := by
  have suffix : Floor 109 42 43024 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor130
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 105 42 41790 := by
  have suffix : Floor 107 42 41790 :=
    weaken (by decide) (by decide) floor124
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G01.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 152 41 64130 := by
  have suffix : Floor 159 41 64130 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor141
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 106 41 41164 := by
  have suffix : Floor 111 41 41164 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor127
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks88404G01.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 151 40 60062 := by
  have suffix : Floor 161 40 60062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor136
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 107 40 39992 := by
  have suffix : Floor 109 40 39992 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor126
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 106 40 39196 := by
  have suffix : Floor 107 40 39196 :=
    weaken (by decide) (by decide) floor119
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G01.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 108 39 38712 := by
  have suffix : Floor 110 39 38712 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor125
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks88404G01.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 106 39 37854 := by
  have suffix : Floor 108 39 37854 :=
    weaken (by decide) (by decide) floor117
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G01.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 161 38 59368 := by
  have suffix : Floor 162 38 59368 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor122
  intro s hs hbig
  by_cases h : s < 162
  · exact SourceCoverChecks88404G01.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 157 38 57032 := by
  have suffix : Floor 159 38 57032 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor133
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 107 38 36606 := by
  have suffix : Floor 109 38 36606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor121
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 105 38 35822 := by
  have suffix : Floor 107 38 35822 :=
    weaken (by decide) (by decide) floor113
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G01.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 159 37 56820 := by
  have suffix : Floor 162 37 56820 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor119
  intro s hs hbig
  by_cases h : s < 162
  · exact SourceCoverChecks88404G01.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 157 37 55630 := by
  have suffix : Floor 159 37 55630 :=
    weaken (by decide) (by decide) floor111
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 106 37 34606 := by
  have suffix : Floor 112 37 34606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor114
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks88404G01.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 159 36 54268 := by
  have suffix : Floor 161 36 54268 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor130
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 157 36 52900 := by
  have suffix : Floor 159 36 52900 :=
    weaken (by decide) (by decide) floor108
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 107 36 33494 := by
  have suffix : Floor 109 36 33494 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor112
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 106 36 32978 := by
  have suffix : Floor 107 36 32978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor036
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G01.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 161 35 50768 := by
  have suffix : Floor 163 35 50768 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor043
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks88404G01.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 159 35 50078 := by
  have suffix : Floor 161 35 50078 :=
    weaken (by decide) (by decide) floor104
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 157 35 49794 := by
  have suffix : Floor 159 35 49794 :=
    weaken (by decide) (by decide) floor103
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 106 35 31526 := by
  have suffix : Floor 108 35 31526 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor108
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G01.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 90 35 25320 := by
  have suffix : Floor 106 35 25320 :=
    weaken (by decide) (by decide) floor101
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G01.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 157 34 47548 := by
  have suffix : Floor 161 34 47548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor266
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 105 34 29664 := by
  have suffix : Floor 109 34 29664 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor106
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 157 33 45160 := by
  have suffix : Floor 158 33 45160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor085
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks88404G01.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 106 33 28079 := by
  have suffix : Floor 109 33 28079 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor102
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 107 32 26993 := by
  have suffix : Floor 113 32 26993 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor095
  intro s hs hbig
  by_cases h : s < 113
  · exact SourceCoverChecks88404G01.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 105 32 26000 := by
  have suffix : Floor 107 32 26000 :=
    weaken (by decide) (by decide) floor095
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks88404G01.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 157 31 39196 := by
  have suffix : Floor 162 31 39196 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor096
  intro s hs hbig
  by_cases h : s < 162
  · exact SourceCoverChecks88404G01.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 106 31 24811 := by
  have suffix : Floor 108 31 24811 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor094
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G01.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 90 31 19941 := by
  have suffix : Floor 102 31 19941 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor072
  intro s hs hbig
  by_cases h : s < 102
  · exact SourceCoverChecks88404G01.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 161 30 38712 := by
  have suffix : Floor 164 30 38712 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor090
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks88404G01.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 157 30 37854 := by
  have suffix : Floor 161 30 37854 :=
    weaken (by decide) (by decide) floor090
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 106 30 23981 := by
  have suffix : Floor 145 30 23981 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor045
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks88404G01.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 90 30 18743 := by
  have suffix : Floor 106 30 18743 :=
    weaken (by decide) (by decide) floor088
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks88404G01.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 157 29 34606 := by
  have suffix : Floor 166 29 34606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor028
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks88404G01.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 106 29 22683 := by
  have suffix : Floor 116 29 22683 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor067
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks88404G01.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 273 28 59548 := by
  have suffix : Floor 279 28 59548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor085
  intro s hs hbig
  by_cases h : s < 279
  · exact SourceCoverChecks88404G01.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 159 28 33494 := by
  have suffix : Floor 162 28 33494 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor084
  intro s hs hbig
  by_cases h : s < 162
  · exact SourceCoverChecks88404G01.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 157 28 32978 := by
  have suffix : Floor 159 28 32978 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks88404G01.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 105 28 21063 := by
  have suffix : Floor 116 28 21063 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor067
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks88404G01.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 157 27 31526 := by
  have suffix : Floor 161 27 31526 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor094
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks88404G01.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 108 27 19819 := by
  have suffix : Floor 111 27 19819 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor080
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks88404G01.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 106 25 17554 := by
  have suffix : Floor 110 25 17554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor076
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks88404G01.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 180 24 29548 := by
  have suffix : Floor 186 24 29548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor075
  intro s hs hbig
  by_cases h : s < 186
  · exact SourceCoverChecks88404G01.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 105 24 14764 := by
  have suffix : Floor 109 24 14764 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor074
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks88404G01.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 184 23 27730 := by
  have suffix : Floor 200 23 27730 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor046
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks88404G01.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 180 23 27164 := by
  have suffix : Floor 184 23 27164 :=
    weaken (by decide) (by decide) floor075
  intro s hs hbig
  by_cases h : s < 184
  · exact SourceCoverChecks88404G01.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 471 22 62624 := by
  have suffix : Floor 472 22 62624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor060
  intro s hs hbig
  by_cases h : s < 472
  · exact SourceCoverChecks88404G01.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 180 22 24811 := by
  have suffix : Floor 220 22 24811 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor061
  intro s hs hbig
  by_cases h : s < 220
  · exact SourceCoverChecks88404G01.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 103 22 13236 := by
  have suffix : Floor 114 22 13236 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor061
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks88404G01.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 469 21 62278 := by
  have suffix : Floor 472 21 62278 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor060
  intro s hs hbig
  by_cases h : s < 472
  · exact SourceCoverChecks88404G01.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 461 21 60062 := by
  have suffix : Floor 462 21 60062 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor012
  intro s hs hbig
  by_cases h : s < 462
  · exact SourceCoverChecks88404G01.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 459 21 59548 := by
  have suffix : Floor 460 21 59548 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor058
  intro s hs hbig
  by_cases h : s < 460
  · exact SourceCoverChecks88404G01.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 458 21 59368 := by
  have suffix : Floor 459 21 59368 :=
    weaken (by decide) (by decide) floor068
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks88404G01.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 450 21 57032 := by
  have suffix : Floor 452 21 57032 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor053
  intro s hs hbig
  by_cases h : s < 452
  · exact SourceCoverChecks88404G01.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 449 21 56820 := by
  have suffix : Floor 450 21 56820 :=
    weaken (by decide) (by decide) floor066
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks88404G01.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 448 21 56698 := by
  have suffix : Floor 449 21 56698 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor033
  intro s hs hbig
  by_cases h : s < 449
  · exact SourceCoverChecks88404G01.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 439 21 54268 := by
  have suffix : Floor 440 21 54268 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor050
  intro s hs hbig
  by_cases h : s < 440
  · exact SourceCoverChecks88404G00.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 434 21 52900 := by
  have suffix : Floor 435 21 52900 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor049
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks88404G00.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 429 21 51738 := by
  have suffix : Floor 431 21 51738 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor051
  intro s hs hbig
  by_cases h : s < 431
  · exact SourceCoverChecks88404G00.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 180 21 23081 := by
  have suffix : Floor 204 21 23081 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor025
  intro s hs hbig
  by_cases h : s < 204
  · exact SourceCoverChecks88404G00.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 106 21 11674 := by
  have suffix : Floor 108 21 11674 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor052
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks88404G00.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 425 20 50768 := by
  have suffix : Floor 426 20 50768 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor044
  intro s hs hbig
  by_cases h : s < 426
  · exact SourceCoverChecks88404G00.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 422 20 50078 := by
  have suffix : Floor 425 20 50078 :=
    weaken (by decide) (by decide) floor058
  intro s hs hbig
  by_cases h : s < 425
  · exact SourceCoverChecks88404G00.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 418 20 49168 := by
  have suffix : Floor 420 20 49168 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor050
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks88404G00.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 401 20 45160 := by
  have suffix : Floor 404 20 45160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor027
  intro s hs hbig
  by_cases h : s < 404
  · exact SourceCoverChecks88404G00.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 400 20 44796 := by
  have suffix : Floor 401 20 44796 :=
    weaken (by decide) (by decide) floor055
  intro s hs hbig
  by_cases h : s < 401
  · exact SourceCoverChecks88404G00.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 399 20 44770 := by
  have suffix : Floor 400 20 44770 :=
    weaken (by decide) (by decide) floor054
  intro s hs hbig
  by_cases h : s < 400
  · exact SourceCoverChecks88404G00.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 395 20 43656 := by
  have suffix : Floor 397 20 43656 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor007
  intro s hs hbig
  by_cases h : s < 397
  · exact SourceCoverChecks88404G00.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 392 20 43024 := by
  have suffix : Floor 395 20 43024 :=
    weaken (by decide) (by decide) floor052
  intro s hs hbig
  by_cases h : s < 395
  · exact SourceCoverChecks88404G00.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 180 20 19941 := by
  have suffix : Floor 192 20 19941 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor039
  intro s hs hbig
  by_cases h : s < 192
  · exact SourceCoverChecks88404G00.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 386 19 41790 := by
  have suffix : Floor 387 19 41790 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor037
  intro s hs hbig
  by_cases h : s < 387
  · exact SourceCoverChecks88404G00.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 384 19 41164 := by
  have suffix : Floor 385 19 41164 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor021
  intro s hs hbig
  by_cases h : s < 385
  · exact SourceCoverChecks88404G00.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 378 19 39992 := by
  have suffix : Floor 379 19 39992 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor045
  intro s hs hbig
  by_cases h : s < 379
  · exact SourceCoverChecks88404G00.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 375 19 39196 := by
  have suffix : Floor 376 19 39196 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor020
  intro s hs hbig
  by_cases h : s < 376
  · exact SourceCoverChecks88404G00.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 372 19 38712 := by
  have suffix : Floor 373 19 38712 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor019
  intro s hs hbig
  by_cases h : s < 373
  · exact SourceCoverChecks88404G00.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 368 19 37854 := by
  have suffix : Floor 372 19 37854 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor038
  intro s hs hbig
  by_cases h : s < 372
  · exact SourceCoverChecks88404G00.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 362 19 36606 := by
  have suffix : Floor 365 19 36606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor044
  intro s hs hbig
  by_cases h : s < 365
  · exact SourceCoverChecks88404G00.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 359 19 35822 := by
  have suffix : Floor 362 19 35822 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor017
  intro s hs hbig
  by_cases h : s < 362
  · exact SourceCoverChecks88404G00.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 180 19 18743 := by
  have suffix : Floor 186 19 18743 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor031
  intro s hs hbig
  by_cases h : s < 186
  · exact SourceCoverChecks88404G00.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 106 19 10010 := by
  have suffix : Floor 117 19 10010 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor011
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks88404G00.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 91 19 8378 := by
  have suffix : Floor 96 19 8378 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor030
  intro s hs hbig
  by_cases h : s < 96
  · exact SourceCoverChecks88404G00.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 90 19 8192 := by
  have suffix : Floor 91 19 8192 :=
    weaken (by decide) (by decide) floor039
  intro s hs hbig
  by_cases h : s < 91
  · exact SourceCoverChecks88404G00.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 353 18 34606 := by
  have suffix : Floor 357 18 34606 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor018
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks88404G00.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 347 18 33494 := by
  have suffix : Floor 350 18 33494 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor019
  intro s hs hbig
  by_cases h : s < 350
  · exact SourceCoverChecks88404G00.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 345 18 32978 := by
  have suffix : Floor 346 18 32978 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor016
  intro s hs hbig
  by_cases h : s < 346
  · exact SourceCoverChecks88404G00.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 337 18 31526 := by
  have suffix : Floor 338 18 31526 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor014
  intro s hs hbig
  by_cases h : s < 338
  · exact SourceCoverChecks88404G00.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 327 18 29664 := by
  have suffix : Floor 328 18 29664 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor041
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks88404G00.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 326 18 29371 := by
  have suffix : Floor 327 18 29371 :=
    weaken (by decide) (by decide) floor033
  intro s hs hbig
  by_cases h : s < 327
  · exact SourceCoverChecks88404G00.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 323 18 28758 := by
  have suffix : Floor 325 18 28758 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor024
  intro s hs hbig
  by_cases h : s < 325
  · exact SourceCoverChecks88404G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 317 18 27730 := by
  have suffix : Floor 321 18 27730 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor013
  intro s hs hbig
  by_cases h : s < 321
  · exact SourceCoverChecks88404G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 311 18 26614 := by
  have suffix : Floor 313 18 26614 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor022
  intro s hs hbig
  by_cases h : s < 313
  · exact SourceCoverChecks88404G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 182 18 16610 := by
  have suffix : Floor 200 18 16610 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor007
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks88404G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 180 18 16216 := by
  have suffix : Floor 182 18 16216 :=
    weaken (by decide) (by decide) floor028
  intro s hs hbig
  by_cases h : s < 182
  · exact SourceCoverChecks88404G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 319 17 28079 := by
  have suffix : Floor 381 17 28079 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor030
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks88404G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 314 17 27164 := by
  have suffix : Floor 319 17 27164 :=
    weaken (by decide) (by decide) floor026
  intro s hs hbig
  by_cases h : s < 319
  · exact SourceCoverChecks88404G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 307 17 26000 := by
  have suffix : Floor 313 17 26000 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor022
  intro s hs hbig
  by_cases h : s < 313
  · exact SourceCoverChecks88404G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 303 17 25320 := by
  have suffix : Floor 307 17 25320 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor021
  intro s hs hbig
  by_cases h : s < 307
  · exact SourceCoverChecks88404G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 300 17 24811 := by
  have suffix : Floor 303 17 24811 :=
    weaken (by decide) (by decide) floor023
  intro s hs hbig
  by_cases h : s < 303
  · exact SourceCoverChecks88404G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 296 17 23981 := by
  have suffix : Floor 298 17 23981 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor003
  intro s hs hbig
  by_cases h : s < 298
  · exact SourceCoverChecks88404G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 290 17 23081 := by
  have suffix : Floor 292 17 23081 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor010
  intro s hs hbig
  by_cases h : s < 292
  · exact SourceCoverChecks88404G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 284 17 22109 := by
  have suffix : Floor 285 17 22109 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor039
  intro s hs hbig
  by_cases h : s < 285
  · exact SourceCoverChecks88404G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 278 16 21063 := by
  have suffix : Floor 570 16 21063 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor042
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks88404G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 270 16 19941 := by
  have suffix : Floor 273 16 19941 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor015
  intro s hs hbig
  by_cases h : s < 273
  · exact SourceCoverChecks88404G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 262 16 18743 := by
  have suffix : Floor 264 16 18743 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor013
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks88404G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 248 16 17554 := by
  have suffix : Floor 250 16 17554 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor012
  intro s hs hbig
  by_cases h : s < 250
  · exact SourceCoverChecks88404G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 241 16 16610 := by
  have suffix : Floor 248 16 16610 :=
    weaken (by decide) (by decide) floor015
  intro s hs hbig
  by_cases h : s < 248
  · exact SourceCoverChecks88404G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 238 16 16216 := by
  have suffix : Floor 241 16 16216 :=
    weaken (by decide) (by decide) floor014
  intro s hs hbig
  by_cases h : s < 241
  · exact SourceCoverChecks88404G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 228 15 14764 := by
  have suffix : Floor 230 15 14764 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor030
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks88404G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 216 15 13236 := by
  have suffix : Floor 218 15 13236 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor047
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks88404G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 106 15 6286 := by
  have suffix : Floor 114 15 6286 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor045
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks88404G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 203 14 11674 := by
  have suffix : Floor 206 14 11674 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor031
  intro s hs hbig
  by_cases h : s < 206
  · exact SourceCoverChecks88404G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 188 14 10010 := by
  have suffix : Floor 190 14 10010 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor003
  intro s hs hbig
  by_cases h : s < 190
  · exact SourceCoverChecks88404G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 174 13 8570 := by
  have suffix : Floor 176 13 8570 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor005
  intro s hs hbig
  by_cases h : s < 176
  · exact SourceCoverChecks88404G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 172 13 8378 := by
  have suffix : Floor 174 13 8378 :=
    weaken (by decide) (by decide) floor007
  intro s hs hbig
  by_cases h : s < 174
  · exact SourceCoverChecks88404G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 171 13 8192 := by
  have suffix : Floor 172 13 8192 :=
    weaken (by decide) (by decide) floor006
  intro s hs hbig
  by_cases h : s < 172
  · exact SourceCoverChecks88404G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 90 13 4313 := by
  have suffix : Floor 129 13 4313 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor004
  intro s hs hbig
  by_cases h : s < 129
  · exact SourceCoverChecks88404G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 150 12 6286 := by
  have suffix : Floor 158 12 6286 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor034
  intro s hs hbig
  by_cases h : s < 158
  · exact SourceCoverChecks88404G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 125 11 4313 := by
  have suffix : Floor 129 11 4313 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor004
  intro s hs hbig
  by_cases h : s < 129
  · exact SourceCoverChecks88404G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 91 10 2259 := by
  have suffix : Floor 93 10 2259 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors94488.floor001
  intro s hs hbig
  by_cases h : s < 93
  · exact SourceCoverChecks88404G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 90 10 2211 := by
  have suffix : Floor 91 10 2211 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 91
  · exact SourceCoverChecks88404G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors88404
