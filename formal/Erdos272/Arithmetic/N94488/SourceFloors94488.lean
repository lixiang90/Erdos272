module

public import Erdos272.Arithmetic.N94488.SourceCoverChecks94488G00
public import Erdos272.Arithmetic.N94488.SourceCoverChecks94488G01
public import Erdos272.Arithmetic.N94488.SourceCoverChecks94488G02
public import Erdos272.Arithmetic.N109474.SourceFloors109474

@[expose] public section

namespace JSP233.SourceFloors94488
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem floor172 : Floor 109 60 77660 := by
  have suffix : Floor 113 60 77660 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor138
  intro s hs hbig
  by_cases h : s < 113
  · exact SourceCoverChecks94488G02.bound0172 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor172

theorem floor171 : Floor 107 60 75086 := by
  have suffix : Floor 109 60 75086 :=
    weaken (by decide) (by decide) floor172
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks94488G02.bound0171 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor171

theorem floor170 : Floor 106 59 71930 := by
  have suffix : Floor 108 59 71930 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor142
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0170 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor170

theorem floor169 : Floor 105 59 70890 := by
  have suffix : Floor 106 59 70890 :=
    weaken (by decide) (by decide) floor170
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks94488G02.bound0169 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor169

theorem floor168 : Floor 104 59 69292 := by
  have suffix : Floor 105 59 69292 :=
    weaken (by decide) (by decide) floor169
  intro s hs hbig
  by_cases h : s < 105
  · exact SourceCoverChecks94488G02.bound0168 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor168

theorem floor167 : Floor 104 58 67988 := by
  have suffix : Floor 108 58 67988 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor141
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0167 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor167

theorem floor166 : Floor 106 57 67632 := by
  have suffix : Floor 108 57 67632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor141
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0166 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor166

theorem floor165 : Floor 104 57 66374 := by
  have suffix : Floor 106 57 66374 :=
    weaken (by decide) (by decide) floor166
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks94488G02.bound0165 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor165

theorem floor164 : Floor 111 56 71018 := by
  have suffix : Floor 114 56 71018 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor131
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0164 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor164

theorem floor163 : Floor 107 56 67126 := by
  have suffix : Floor 110 56 67126 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor139
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks94488G02.bound0163 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor163

theorem floor162 : Floor 105 56 64488 := by
  have suffix : Floor 107 56 64488 :=
    weaken (by decide) (by decide) floor163
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks94488G02.bound0162 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor162

theorem floor161 : Floor 106 55 64132 := by
  have suffix : Floor 108 55 64132 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor138
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0161 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor161

theorem floor160 : Floor 104 55 63242 := by
  have suffix : Floor 106 55 63242 :=
    weaken (by decide) (by decide) floor161
  intro s hs hbig
  by_cases h : s < 106
  · exact SourceCoverChecks94488G02.bound0160 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor160

theorem floor159 : Floor 105 54 61580 := by
  have suffix : Floor 108 54 61580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor134
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0159 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor159

theorem floor158 : Floor 110 53 64160 := by
  have suffix : Floor 114 53 64160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor167
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0158 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor158

theorem floor157 : Floor 106 53 61202 := by
  have suffix : Floor 108 53 61202 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor134
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0157 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor157

theorem floor156 : Floor 109 52 61410 := by
  have suffix : Floor 115 52 61410 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor162
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks94488G02.bound0156 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor156

theorem floor155 : Floor 105 52 58732 := by
  have suffix : Floor 108 52 58732 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor130
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0155 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor155

theorem floor154 : Floor 146 51 88468 := by
  have suffix : Floor 150 51 88468 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor126
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks94488G02.bound0154 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor154

theorem floor153 : Floor 114 51 63190 := by
  have suffix : Floor 115 51 63190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor162
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks94488G02.bound0153 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor153

theorem floor152 : Floor 106 51 57712 := by
  have suffix : Floor 108 51 57712 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor130
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0152 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor152

theorem floor151 : Floor 106 50 55658 := by
  have suffix : Floor 108 50 55658 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor126
  intro s hs hbig
  by_cases h : s < 108
  · exact SourceCoverChecks94488G02.bound0151 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor151

theorem floor150 : Floor 112 49 57624 := by
  have suffix : Floor 115 49 57624 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor159
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks94488G02.bound0150 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor150

theorem floor149 : Floor 109 48 54588 := by
  have suffix : Floor 112 48 54588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor125
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks94488G02.bound0149 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor149

theorem floor148 : Floor 107 48 53284 := by
  have suffix : Floor 109 48 53284 :=
    weaken (by decide) (by decide) floor149
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks94488G02.bound0148 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor148

theorem floor147 : Floor 147 47 77660 := by
  have suffix : Floor 150 47 77660 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor118
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks94488G02.bound0147 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor147

theorem floor146 : Floor 144 47 75086 := by
  have suffix : Floor 147 47 75086 :=
    weaken (by decide) (by decide) floor147
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks94488G02.bound0146 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor146

theorem floor145 : Floor 142 46 71930 := by
  have suffix : Floor 148 46 71930 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors243614.floor026
  intro s hs hbig
  by_cases h : s < 148
  · exact SourceCoverChecks94488G02.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 141 46 70890 := by
  have suffix : Floor 142 46 70890 :=
    weaken (by decide) (by decide) floor145
  intro s hs hbig
  by_cases h : s < 142
  · exact SourceCoverChecks94488G02.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 139 46 69292 := by
  have suffix : Floor 141 46 69292 :=
    weaken (by decide) (by decide) floor144
  intro s hs hbig
  by_cases h : s < 141
  · exact SourceCoverChecks94488G02.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 109 46 51002 := by
  have suffix : Floor 114 46 51002 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor153
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 107 46 49742 := by
  have suffix : Floor 109 46 49742 :=
    weaken (by decide) (by decide) floor142
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks94488G02.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 144 45 69896 := by
  have suffix : Floor 147 45 69896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor062
  intro s hs hbig
  by_cases h : s < 147
  · exact SourceCoverChecks94488G02.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 139 45 67988 := by
  have suffix : Floor 140 45 67988 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor105
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks94488G02.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 114 45 52688 := by
  have suffix : Floor 116 45 52688 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor113
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G02.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 112 45 51146 := by
  have suffix : Floor 114 45 51146 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor153
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 139 44 64488 := by
  have suffix : Floor 145 44 64488 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor061
  intro s hs hbig
  by_cases h : s < 145
  · exact SourceCoverChecks94488G02.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 111 44 48774 := by
  have suffix : Floor 116 44 48774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor112
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G02.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 109 44 47344 := by
  have suffix : Floor 111 44 47344 :=
    weaken (by decide) (by decide) floor135
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks94488G02.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 146 43 64948 := by
  have suffix : Floor 159 43 64948 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor141
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks94488G02.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 139 43 61580 := by
  have suffix : Floor 146 43 61580 :=
    weaken (by decide) (by decide) floor133
  intro s hs hbig
  by_cases h : s < 146
  · exact SourceCoverChecks94488G02.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 110 43 46770 := by
  have suffix : Floor 116 43 46770 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor112
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G02.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 109 42 44448 := by
  have suffix : Floor 114 42 44448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor140
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 112 41 44258 := by
  have suffix : Floor 114 41 44258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor140
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G02.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 171 40 71018 := by
  have suffix : Floor 177 40 71018 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor079
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks94488G02.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 111 40 41986 := by
  have suffix : Floor 118 40 41986 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor099
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks94488G01.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 109 40 40854 := by
  have suffix : Floor 111 40 40854 :=
    weaken (by decide) (by decide) floor127
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks94488G01.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 110 39 39762 := by
  have suffix : Floor 116 39 39762 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor098
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G01.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 171 38 63190 := by
  have suffix : Floor 175 38 63190 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor097
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks94488G01.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 166 38 61410 := by
  have suffix : Floor 171 38 61410 :=
    weaken (by decide) (by decide) floor124
  intro s hs hbig
  by_cases h : s < 171
  · exact SourceCoverChecks94488G01.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 162 38 60452 := by
  have suffix : Floor 166 38 60452 :=
    weaken (by decide) (by decide) floor123
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks94488G01.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 109 38 37610 := by
  have suffix : Floor 115 38 37610 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor096
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks94488G01.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 164 37 58560 := by
  have suffix : Floor 175 37 58560 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor092
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks94488G01.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 162 37 57712 := by
  have suffix : Floor 164 37 57712 :=
    weaken (by decide) (by decide) floor120
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks94488G01.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 114 37 37325 := by
  have suffix : Floor 117 37 37325 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor089
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks94488G01.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 96 37 29912 := by
  have suffix : Floor 107 37 29912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors118533.floor036
  intro s hs hbig
  by_cases h : s < 107
  · exact SourceCoverChecks94488G01.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 184 36 64160 := by
  have suffix : Floor 191 36 64160 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor086
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks94488G01.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 164 36 55810 := by
  have suffix : Floor 175 36 55810 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor090
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks94488G01.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 112 36 35303 := by
  have suffix : Floor 117 36 35303 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor089
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks94488G01.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 111 36 34314 := by
  have suffix : Floor 112 36 34314 :=
    weaken (by decide) (by decide) floor114
  intro s hs hbig
  by_cases h : s < 112
  · exact SourceCoverChecks94488G01.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 109 36 34034 := by
  have suffix : Floor 111 36 34034 :=
    weaken (by decide) (by decide) floor113
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks94488G01.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 260 35 88468 := by
  have suffix : Floor 300 35 88468 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor082
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks94488G01.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 162 35 49742 := by
  have suffix : Floor 163 35 49742 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor043
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks94488G01.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 110 35 32688 := by
  have suffix : Floor 116 35 32688 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor085
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G01.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 108 35 31742 := by
  have suffix : Floor 110 35 31742 :=
    weaken (by decide) (by decide) floor109
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks94488G01.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 168 34 51146 := by
  have suffix : Floor 169 34 51146 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor268
  intro s hs hbig
  by_cases h : s < 169
  · exact SourceCoverChecks94488G01.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 109 34 30413 := by
  have suffix : Floor 114 34 30413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor119
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G01.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 94 34 24452 := by
  have suffix : Floor 109 34 24452 :=
    weaken (by decide) (by decide) floor106
  intro s hs hbig
  by_cases h : s < 109
  · exact SourceCoverChecks94488G01.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 166 33 48774 := by
  have suffix : Floor 175 33 48774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor081
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks94488G01.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 162 33 47344 := by
  have suffix : Floor 166 33 47344 :=
    weaken (by decide) (by decide) floor104
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks94488G01.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 109 33 28478 := by
  have suffix : Floor 110 33 28478 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor094
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks94488G01.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 168 32 44258 := by
  have suffix : Floor 175 32 44258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor076
  intro s hs hbig
  by_cases h : s < 175
  · exact SourceCoverChecks94488G01.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 93 32 22705 := by
  have suffix : Floor 102 32 22705 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor072
  intro s hs hbig
  by_cases h : s < 102
  · exact SourceCoverChecks94488G01.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 294 31 77660 := by
  have suffix : Floor 300 31 77660 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor074
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks94488G01.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 288 31 75086 := by
  have suffix : Floor 294 31 75086 :=
    weaken (by decide) (by decide) floor099
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks94488G01.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 166 31 41986 := by
  have suffix : Floor 204 31 41986 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor068
  intro s hs hbig
  by_cases h : s < 204
  · exact SourceCoverChecks94488G01.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 162 31 40854 := by
  have suffix : Floor 166 31 40854 :=
    weaken (by decide) (by decide) floor097
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks94488G01.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 113 31 27100 := by
  have suffix : Floor 116 31 27100 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor073
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G01.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 108 31 25924 := by
  have suffix : Floor 113 31 25924 :=
    weaken (by decide) (by decide) floor095
  intro s hs hbig
  by_cases h : s < 113
  · exact SourceCoverChecks94488G01.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 285 30 71930 := by
  have suffix : Floor 289 30 71930 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor231
  intro s hs hbig
  by_cases h : s < 289
  · exact SourceCoverChecks94488G01.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 282 30 70890 := by
  have suffix : Floor 285 30 70890 :=
    weaken (by decide) (by decide) floor093
  intro s hs hbig
  by_cases h : s < 285
  · exact SourceCoverChecks94488G01.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 260 30 64948 := by
  have suffix : Floor 264 30 64948 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor053
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks94488G01.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 164 30 39762 := by
  have suffix : Floor 195 30 39762 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor086
  intro s hs hbig
  by_cases h : s < 195
  · exact SourceCoverChecks94488G01.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 162 30 37610 := by
  have suffix : Floor 164 30 37610 :=
    weaken (by decide) (by decide) floor090
  intro s hs hbig
  by_cases h : s < 164
  · exact SourceCoverChecks94488G01.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 288 29 69896 := by
  have suffix : Floor 294 29 69896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor042
  intro s hs hbig
  by_cases h : s < 294
  · exact SourceCoverChecks94488G01.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 282 29 67632 := by
  have suffix : Floor 288 29 67632 :=
    weaken (by decide) (by decide) floor088
  intro s hs hbig
  by_cases h : s < 288
  · exact SourceCoverChecks94488G01.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 279 29 66374 := by
  have suffix : Floor 282 29 66374 :=
    weaken (by decide) (by decide) floor087
  intro s hs hbig
  by_cases h : s < 282
  · exact SourceCoverChecks94488G01.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 279 28 61580 := by
  have suffix : Floor 342 28 61580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor104
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks94488G01.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 162 28 34034 := by
  have suffix : Floor 165 28 34034 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor029
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks94488G01.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 112 27 20370 := by
  have suffix : Floor 161 27 20370 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor094
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks94488G01.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 192 26 35303 := by
  have suffix : Floor 205 26 35303 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors233811.floor037
  intro s hs hbig
  by_cases h : s < 205
  · exact SourceCoverChecks94488G01.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 190 26 34314 := by
  have suffix : Floor 191 26 34314 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor062
  intro s hs hbig
  by_cases h : s < 191
  · exact SourceCoverChecks94488G01.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 111 26 19908 := by
  have suffix : Floor 177 26 19908 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor051
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks94488G01.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 107 26 18908 := by
  have suffix : Floor 111 26 18908 :=
    weaken (by decide) (by decide) floor080
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks94488G01.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 188 25 32688 := by
  have suffix : Floor 200 25 32688 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor061
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks94488G01.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 186 25 32413 := by
  have suffix : Floor 188 25 32413 :=
    weaken (by decide) (by decide) floor078
  intro s hs hbig
  by_cases h : s < 188
  · exact SourceCoverChecks94488G01.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 110 25 17920 := by
  have suffix : Floor 182 25 17920 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors190000.floor041
  intro s hs hbig
  by_cases h : s < 182
  · exact SourceCoverChecks94488G01.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 186 24 30413 := by
  have suffix : Floor 200 24 30413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor061
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks94488G01.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 109 24 15928 := by
  have suffix : Floor 116 24 15928 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor045
  intro s hs hbig
  by_cases h : s < 116
  · exact SourceCoverChecks94488G01.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 557 23 88468 := by
  have suffix : Floor 558 23 88468 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor059
  intro s hs hbig
  by_cases h : s < 558
  · exact SourceCoverChecks94488G01.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 523 23 77660 := by
  have suffix : Floor 525 23 77660 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor050
  intro s hs hbig
  by_cases h : s < 525
  · exact SourceCoverChecks94488G01.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 514 23 75086 := by
  have suffix : Floor 515 23 75086 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor048
  intro s hs hbig
  by_cases h : s < 515
  · exact SourceCoverChecks94488G01.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 196 23 27100 := by
  have suffix : Floor 200 23 27100 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor046
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks94488G01.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 186 23 25924 := by
  have suffix : Floor 196 23 25924 :=
    weaken (by decide) (by decide) floor070
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks94488G01.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 503 22 71930 := by
  have suffix : Floor 504 22 71930 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor043
  intro s hs hbig
  by_cases h : s < 504
  · exact SourceCoverChecks94488G01.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 500 22 70890 := by
  have suffix : Floor 501 22 70890 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor042
  intro s hs hbig
  by_cases h : s < 501
  · exact SourceCoverChecks94488G01.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 497 22 69896 := by
  have suffix : Floor 498 22 69896 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor064
  intro s hs hbig
  by_cases h : s < 498
  · exact SourceCoverChecks94488G01.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 495 22 69292 := by
  have suffix : Floor 496 22 69292 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor041
  intro s hs hbig
  by_cases h : s < 496
  · exact SourceCoverChecks94488G01.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 489 22 67632 := by
  have suffix : Floor 490 22 67632 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor039
  intro s hs hbig
  by_cases h : s < 490
  · exact SourceCoverChecks94488G01.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 487 22 67126 := by
  have suffix : Floor 489 22 67126 :=
    weaken (by decide) (by decide) floor064
  intro s hs hbig
  by_cases h : s < 489
  · exact SourceCoverChecks94488G00.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 484 22 66374 := by
  have suffix : Floor 485 22 66374 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor062
  intro s hs hbig
  by_cases h : s < 485
  · exact SourceCoverChecks94488G00.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 477 22 64488 := by
  have suffix : Floor 479 22 64488 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor038
  intro s hs hbig
  by_cases h : s < 479
  · exact SourceCoverChecks94488G00.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 476 22 64160 := by
  have suffix : Floor 477 22 64160 :=
    weaken (by decide) (by decide) floor061
  intro s hs hbig
  by_cases h : s < 477
  · exact SourceCoverChecks94488G00.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 188 22 24452 := by
  have suffix : Floor 220 22 24452 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor061
  intro s hs hbig
  by_cases h : s < 220
  · exact SourceCoverChecks94488G00.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 467 21 61580 := by
  have suffix : Floor 469 21 61580 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor036
  intro s hs hbig
  by_cases h : s < 469
  · exact SourceCoverChecks94488G00.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 465 21 61202 := by
  have suffix : Floor 466 21 61202 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor035
  intro s hs hbig
  by_cases h : s < 466
  · exact SourceCoverChecks94488G00.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 463 21 60452 := by
  have suffix : Floor 465 21 60452 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 465
  · exact SourceCoverChecks94488G00.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 456 21 58732 := by
  have suffix : Floor 460 21 58732 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor058
  intro s hs hbig
  by_cases h : s < 460
  · exact SourceCoverChecks94488G00.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 455 21 58560 := by
  have suffix : Floor 456 21 58560 :=
    weaken (by decide) (by decide) floor055
  intro s hs hbig
  by_cases h : s < 456
  · exact SourceCoverChecks94488G00.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 452 21 57712 := by
  have suffix : Floor 453 21 57712 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor034
  intro s hs hbig
  by_cases h : s < 453
  · exact SourceCoverChecks94488G00.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 445 21 55810 := by
  have suffix : Floor 446 21 55810 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor057
  intro s hs hbig
  by_cases h : s < 446
  · exact SourceCoverChecks94488G00.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 444 21 55658 := by
  have suffix : Floor 445 21 55658 :=
    weaken (by decide) (by decide) floor052
  intro s hs hbig
  by_cases h : s < 445
  · exact SourceCoverChecks94488G00.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 440 21 54588 := by
  have suffix : Floor 442 21 54588 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor032
  intro s hs hbig
  by_cases h : s < 442
  · exact SourceCoverChecks94488G00.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 435 21 53284 := by
  have suffix : Floor 438 21 53284 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor031
  intro s hs hbig
  by_cases h : s < 438
  · exact SourceCoverChecks94488G00.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 433 21 52688 := by
  have suffix : Floor 435 21 52688 :=
    weaken (by decide) (by decide) floor049
  intro s hs hbig
  by_cases h : s < 435
  · exact SourceCoverChecks94488G00.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 186 21 22705 := by
  have suffix : Floor 202 21 22705 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor024
  intro s hs hbig
  by_cases h : s < 202
  · exact SourceCoverChecks94488G00.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 146 21 17937 := by
  have suffix : Floor 186 21 17937 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 186
  · exact SourceCoverChecks94488G00.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 108 21 12567 := by
  have suffix : Floor 110 21 12567 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor053
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks94488G00.bound0045 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 426 20 51146 := by
  have suffix : Floor 431 20 51146 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor051
  intro s hs hbig
  by_cases h : s < 431
  · exact SourceCoverChecks94488G00.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 417 20 48774 := by
  have suffix : Floor 420 20 48774 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor050
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks94488G00.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 408 20 46770 := by
  have suffix : Floor 409 20 46770 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor049
  intro s hs hbig
  by_cases h : s < 409
  · exact SourceCoverChecks94488G00.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 398 20 44448 := by
  have suffix : Floor 402 20 44448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor059
  intro s hs hbig
  by_cases h : s < 402
  · exact SourceCoverChecks94488G00.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 397 20 44258 := by
  have suffix : Floor 398 20 44258 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor048
  intro s hs hbig
  by_cases h : s < 398
  · exact SourceCoverChecks94488G00.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 192 20 20370 := by
  have suffix : Floor 200 20 20370 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor023
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks94488G00.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 190 20 19908 := by
  have suffix : Floor 192 20 19908 :=
    weaken (by decide) (by decide) floor039
  intro s hs hbig
  by_cases h : s < 192
  · exact SourceCoverChecks94488G00.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 387 19 41986 := by
  have suffix : Floor 389 19 41986 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor047
  intro s hs hbig
  by_cases h : s < 389
  · exact SourceCoverChecks94488G00.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 382 19 40854 := by
  have suffix : Floor 385 19 40854 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor021
  intro s hs hbig
  by_cases h : s < 385
  · exact SourceCoverChecks94488G00.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 377 19 39762 := by
  have suffix : Floor 379 19 39762 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor045
  intro s hs hbig
  by_cases h : s < 379
  · exact SourceCoverChecks94488G00.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 367 19 37610 := by
  have suffix : Floor 368 19 37610 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor018
  intro s hs hbig
  by_cases h : s < 368
  · exact SourceCoverChecks94488G00.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 366 19 37325 := by
  have suffix : Floor 367 19 37325 :=
    weaken (by decide) (by decide) floor034
  intro s hs hbig
  by_cases h : s < 367
  · exact SourceCoverChecks94488G00.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 356 19 35303 := by
  have suffix : Floor 360 19 35303 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor036
  intro s hs hbig
  by_cases h : s < 360
  · exact SourceCoverChecks94488G00.bound0032 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 186 19 18908 := by
  have suffix : Floor 216 19 18908 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor043
  intro s hs hbig
  by_cases h : s < 216
  · exact SourceCoverChecks94488G00.bound0031 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 96 19 9401 := by
  have suffix : Floor 117 19 9401 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor011
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks94488G00.bound0030 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor030

theorem floor029 : Floor 351 18 34314 := by
  have suffix : Floor 353 18 34314 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor019
  intro s hs hbig
  by_cases h : s < 353
  · exact SourceCoverChecks94488G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 350 18 34034 := by
  have suffix : Floor 351 18 34034 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks94488G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 343 18 32688 := by
  have suffix : Floor 346 18 32688 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor016
  intro s hs hbig
  by_cases h : s < 346
  · exact SourceCoverChecks94488G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 338 18 31742 := by
  have suffix : Floor 342 18 31742 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor015
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks94488G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 329 18 29912 := by
  have suffix : Floor 331 18 29912 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor042
  intro s hs hbig
  by_cases h : s < 331
  · exact SourceCoverChecks94488G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 325 18 29236 := by
  have suffix : Floor 328 18 29236 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor041
  intro s hs hbig
  by_cases h : s < 328
  · exact SourceCoverChecks94488G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 186 18 15928 := by
  have suffix : Floor 200 18 15928 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor007
  intro s hs hbig
  by_cases h : s < 200
  · exact SourceCoverChecks94488G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 313 17 27100 := by
  have suffix : Floor 381 17 27100 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor030
  intro s hs hbig
  by_cases h : s < 381
  · exact SourceCoverChecks94488G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 307 17 25924 := by
  have suffix : Floor 313 17 25924 :=
    weaken (by decide) (by decide) floor022
  intro s hs hbig
  by_cases h : s < 313
  · exact SourceCoverChecks94488G00.bound0021 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 298 17 24452 := by
  have suffix : Floor 307 17 24452 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 307
  · exact SourceCoverChecks94488G00.bound0020 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 288 17 22705 := by
  have suffix : Floor 289 17 22705 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor009
  intro s hs hbig
  by_cases h : s < 289
  · exact SourceCoverChecks94488G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 111 17 9204 := by
  have suffix : Floor 159 17 9204 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor053
  intro s hs hbig
  by_cases h : s < 159
  · exact SourceCoverChecks94488G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 110 17 9009 := by
  have suffix : Floor 111 17 9009 :=
    weaken (by decide) (by decide) floor018
  intro s hs hbig
  by_cases h : s < 111
  · exact SourceCoverChecks94488G00.bound0017 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 108 17 8760 := by
  have suffix : Floor 110 17 8760 :=
    weaken (by decide) (by decide) floor017
  intro s hs hbig
  by_cases h : s < 110
  · exact SourceCoverChecks94488G00.bound0016 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 273 16 20370 := by
  have suffix : Floor 570 16 20370 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor042
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks94488G00.bound0015 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 270 16 19908 := by
  have suffix : Floor 273 16 19908 :=
    weaken (by decide) (by decide) floor015
  intro s hs hbig
  by_cases h : s < 273
  · exact SourceCoverChecks94488G00.bound0014 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 264 16 18908 := by
  have suffix : Floor 270 16 18908 :=
    weaken (by decide) (by decide) floor014
  intro s hs hbig
  by_cases h : s < 270
  · exact SourceCoverChecks94488G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 250 16 17937 := by
  have suffix : Floor 264 16 17937 :=
    weaken (by decide) (by decide) floor013
  intro s hs hbig
  by_cases h : s < 264
  · exact SourceCoverChecks94488G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 236 15 15928 := by
  have suffix : Floor 258 15 15928 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor006
  intro s hs hbig
  by_cases h : s < 258
  · exact SourceCoverChecks94488G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 210 15 12567 := by
  have suffix : Floor 211 15 12567 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor033
  intro s hs hbig
  by_cases h : s < 211
  · exact SourceCoverChecks94488G00.bound0010 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 182 14 9401 := by
  have suffix : Floor 190 14 9401 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor003
  intro s hs hbig
  by_cases h : s < 190
  · exact SourceCoverChecks94488G00.bound0009 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 93 14 4616 := by
  have suffix : Floor 130 14 4616 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor025
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks94488G00.bound0008 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 196 13 9204 := by
  have suffix : Floor 342 13 9204 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors142758.floor035
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks94488G00.bound0007 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 179 13 9009 := by
  have suffix : Floor 196 13 9009 :=
    weaken (by decide) (by decide) floor007
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks94488G00.bound0006 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 176 13 8760 := by
  have suffix : Floor 179 13 8760 :=
    weaken (by decide) (by decide) floor006
  intro s hs hbig
  by_cases h : s < 179
  · exact SourceCoverChecks94488G00.bound0005 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor005

theorem floor004 : Floor 129 11 4616 := by
  have suffix : Floor 130 11 4616 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors130000.floor025
  intro s hs hbig
  by_cases h : s < 130
  · exact SourceCoverChecks94488G00.bound0004 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 95 10 2475 := by
  have suffix : Floor 101 10 2475 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor001
  intro s hs hbig
  by_cases h : s < 101
  · exact SourceCoverChecks94488G00.bound0003 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 94 10 2425 := by
  have suffix : Floor 95 10 2425 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 95
  · exact SourceCoverChecks94488G00.bound0002 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 93 10 2375 := by
  have suffix : Floor 94 10 2375 :=
    weaken (by decide) (by decide) floor002
  intro s hs hbig
  by_cases h : s < 94
  · exact SourceCoverChecks94488G00.bound0001 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor001

theorem floor000 : Floor 108 9 2529 := by
  have suffix : Floor 114 9 2529 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors109474.floor000
  intro s hs hbig
  by_cases h : s < 114
  · exact SourceCoverChecks94488G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors94488
