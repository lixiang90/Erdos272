module

public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G00
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G01
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G02
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G03
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G04
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G05
public import Erdos272.Arithmetic.N142758.SourceCoverChecks142758G06
public import Erdos272.Arithmetic.N150465.SourceFloors150465

@[expose] public section

namespace JSP233.SourceFloors142758
open SourceFloorSound291012 PureSource208 LowResourceBridges3040
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem join001_00 : ∀ s, 3680 ≤ s → s < 4525 → 7057 ≤ physicalK s 3 :=
  append_cover SourceCoverChecks142758G00.bound0001 SourceCoverChecks142758G00.bound0002
#print axioms join001_00

theorem join001_01 : ∀ s, 4525 ≤ s → s < 5529 → 7057 ≤ physicalK s 3 :=
  append_cover SourceCoverChecks142758G00.bound0003 SourceCoverChecks142758G00.bound0004
#print axioms join001_01

theorem join001_02 : ∀ s, 5529 ≤ s → s < 6553 → 7057 ≤ physicalK s 3 :=
  append_cover SourceCoverChecks142758G00.bound0005 SourceCoverChecks142758G00.bound0006
#print axioms join001_02

theorem join001_03 : ∀ s, 6553 ≤ s → s < 7577 → 7057 ≤ physicalK s 3 :=
  append_cover SourceCoverChecks142758G00.bound0007 SourceCoverChecks142758G00.bound0008
#print axioms join001_03

theorem join001_04 : ∀ s, 7577 ≤ s → s < 8237 → 7057 ≤ physicalK s 3 :=
  append_cover SourceCoverChecks142758G00.bound0009 SourceCoverChecks142758G00.bound0010
#print axioms join001_04

theorem join001_05 : ∀ s, 3680 ≤ s → s < 5529 → 7057 ≤ physicalK s 3 :=
  append_cover join001_00 join001_01
#print axioms join001_05

theorem join001_06 : ∀ s, 5529 ≤ s → s < 7577 → 7057 ≤ physicalK s 3 :=
  append_cover join001_02 join001_03
#print axioms join001_06

theorem join001_07 : ∀ s, 3680 ≤ s → s < 7577 → 7057 ≤ physicalK s 3 :=
  append_cover join001_05 join001_06
#print axioms join001_07

theorem join001_08 : ∀ s, 3680 ≤ s → s < 8237 → 7057 ≤ physicalK s 3 :=
  append_cover join001_07 join001_04
#print axioms join001_08

theorem join005_00 : ∀ s, 1150 ≤ s → s < 2224 → 7057 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks142758G00.bound0014 SourceCoverChecks142758G00.bound0015
#print axioms join005_00

theorem join005_01 : ∀ s, 2224 ≤ s → s < 3299 → 7057 ≤ physicalK s 5 :=
  append_cover SourceCoverChecks142758G00.bound0016 SourceCoverChecks142758G00.bound0017
#print axioms join005_01

theorem join005_02 : ∀ s, 1150 ≤ s → s < 3299 → 7057 ≤ physicalK s 5 :=
  append_cover join005_00 join005_01
#print axioms join005_02

theorem join008_00 : ∀ s, 4160 ≤ s → s < 4800 → 39469 ≤ physicalK s 6 :=
  append_cover SourceCoverChecks142758G00.bound0020 SourceCoverChecks142758G00.bound0021
#print axioms join008_00

theorem join017_00 : ∀ s, 4160 ≤ s → s < 4782 → 81413 ≤ physicalK s 8 :=
  append_cover SourceCoverChecks142758G00.bound0030 SourceCoverChecks142758G00.bound0031
#print axioms join017_00

theorem join017_01 : ∀ s, 4160 ≤ s → s < 4896 → 81413 ≤ physicalK s 8 :=
  append_cover join017_00 SourceCoverChecks142758G01.bound0032
#print axioms join017_01

theorem floor197 : Floor 115 76 123786 := by
  have suffix : Floor 117 76 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor067
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0212 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor197

theorem floor196 : Floor 114 75 119702 := by
  have suffix : Floor 117 75 119702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor066
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0211 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor196

theorem floor195 : Floor 115 74 119046 := by
  have suffix : Floor 117 74 119046 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor066
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0210 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor195

theorem floor194 : Floor 114 73 115034 := by
  have suffix : Floor 118 73 115034 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor056
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G06.bound0209 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor194

theorem floor193 : Floor 115 72 113448 := by
  have suffix : Floor 119 72 113448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor053
  intro s hs hbig
  by_cases h : s < 119
  · exact SourceCoverChecks142758G06.bound0208 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor193

theorem floor192 : Floor 114 71 109544 := by
  have suffix : Floor 117 71 109544 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor065
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0207 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor192

theorem floor191 : Floor 115 70 107584 := by
  have suffix : Floor 118 70 107584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor055
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G06.bound0206 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor191

theorem floor190 : Floor 114 69 103808 := by
  have suffix : Floor 117 69 103808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor064
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0205 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor190

theorem floor189 : Floor 115 68 102866 := by
  have suffix : Floor 117 68 102866 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor064
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0204 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor189

theorem floor188 : Floor 114 67 99186 := by
  have suffix : Floor 120 67 99186 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor117
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks142758G06.bound0203 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor188

theorem floor187 : Floor 115 66 97810 := by
  have suffix : Floor 120 66 97810 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor117
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks142758G06.bound0202 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor187

theorem floor186 : Floor 114 65 94250 := by
  have suffix : Floor 117 65 94250 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor063
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0201 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor186

theorem floor185 : Floor 115 64 92724 := by
  have suffix : Floor 117 64 92724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor063
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0200 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor185

theorem floor184 : Floor 130 63 108096 := by
  have suffix : Floor 140 63 108096 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor125
  intro s hs hbig
  by_cases h : s < 140
  · exact SourceCoverChecks142758G06.bound0199 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor184

theorem floor183 : Floor 114 63 89288 := by
  have suffix : Floor 118 63 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor054
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G06.bound0198 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor183

theorem floor182 : Floor 115 62 88100 := by
  have suffix : Floor 122 62 88100 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor115
  intro s hs hbig
  by_cases h : s < 122
  · exact SourceCoverChecks142758G06.bound0197 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor182

theorem floor181 : Floor 114 61 84792 := by
  have suffix : Floor 117 61 84792 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor017
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0196 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor181

theorem floor180 : Floor 115 60 83568 := by
  have suffix : Floor 117 60 83568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor017
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G06.bound0195 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor180

theorem floor179 : Floor 161 58 123786 := by
  have suffix : Floor 163 58 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor062
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G06.bound0194 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor179

theorem floor178 : Floor 159 57 119702 := by
  have suffix : Floor 163 57 119702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor060
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G06.bound0193 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor178

theorem floor177 : Floor 115 57 77356 := by
  have suffix : Floor 118 57 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor052
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G06.bound0192 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor177

theorem floor176 : Floor 114 57 76424 := by
  have suffix : Floor 115 57 76424 :=
    weaken (by decide) (by decide) floor177
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G05.bound0191 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor176

theorem floor175 : Floor 161 56 119046 := by
  have suffix : Floor 163 56 119046 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor060
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G05.bound0190 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor175

theorem floor174 : Floor 159 56 115034 := by
  have suffix : Floor 161 56 115034 :=
    weaken (by decide) (by decide) floor175
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G05.bound0189 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor174

theorem floor173 : Floor 161 55 113448 := by
  have suffix : Floor 166 55 113448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor048
  intro s hs hbig
  by_cases h : s < 166
  · exact SourceCoverChecks142758G05.bound0188 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor173

theorem floor172 : Floor 159 54 109544 := by
  have suffix : Floor 163 54 109544 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor059
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G05.bound0187 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor172

theorem floor171 : Floor 115 54 71302 := by
  have suffix : Floor 117 54 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor058
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G05.bound0186 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor171

theorem floor170 : Floor 161 53 107584 := by
  have suffix : Floor 165 53 107584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor050
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks142758G05.bound0185 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor170

theorem floor169 : Floor 159 53 103808 := by
  have suffix : Floor 161 53 103808 :=
    weaken (by decide) (by decide) floor170
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G05.bound0184 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor169

theorem floor168 : Floor 130 53 81413 := by
  have suffix : Floor 153 53 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor119
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks142758G05.bound0183 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor168

theorem floor167 : Floor 114 53 68392 := by
  have suffix : Floor 117 53 68392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor015
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G05.bound0182 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor167

theorem floor166 : Floor 161 52 102866 := by
  have suffix : Floor 163 52 102866 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor057
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G05.bound0181 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor166

theorem floor165 : Floor 159 51 99186 := by
  have suffix : Floor 168 51 99186 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor102
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks142758G05.bound0180 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor165

theorem floor164 : Floor 161 50 97810 := by
  have suffix : Floor 168 50 97810 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor102
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks142758G05.bound0179 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor164

theorem floor163 : Floor 159 50 94250 := by
  have suffix : Floor 161 50 94250 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor398
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G05.bound0178 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor163

theorem floor162 : Floor 115 50 63298 := by
  have suffix : Floor 118 50 63298 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor049
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G05.bound0177 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor162

theorem floor161 : Floor 182 49 108096 := by
  have suffix : Floor 196 49 108096 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor110
  intro s hs hbig
  by_cases h : s < 196
  · exact SourceCoverChecks142758G05.bound0176 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor161

theorem floor160 : Floor 159 48 89288 := by
  have suffix : Floor 165 48 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor048
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks142758G05.bound0175 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor160

theorem floor159 : Floor 115 48 59197 := by
  have suffix : Floor 129 48 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor084
  intro s hs hbig
  by_cases h : s < 129
  · exact SourceCoverChecks142758G05.bound0174 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor159

theorem floor158 : Floor 114 48 57486 := by
  have suffix : Floor 115 48 57486 :=
    weaken (by decide) (by decide) floor159
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G05.bound0173 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor158

theorem floor157 : Floor 161 46 83568 := by
  have suffix : Floor 163 46 83568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor014
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G05.bound0172 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor157

theorem floor156 : Floor 115 46 54629 := by
  have suffix : Floor 120 46 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor095
  intro s hs hbig
  by_cases h : s < 120
  · exact SourceCoverChecks142758G05.bound0171 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor156

theorem floor155 : Floor 230 45 123786 := by
  have suffix : Floor 234 45 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor054
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G05.bound0170 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor155

theorem floor154 : Floor 228 45 119702 := by
  have suffix : Floor 230 45 119702 :=
    weaken (by decide) (by decide) floor155
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G05.bound0169 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor154

theorem floor153 : Floor 114 45 52444 := by
  have suffix : Floor 118 45 52444 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor046
  intro s hs hbig
  by_cases h : s < 118
  · exact SourceCoverChecks142758G05.bound0168 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor153

theorem floor152 : Floor 230 44 119046 := by
  have suffix : Floor 234 44 119046 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor052
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G05.bound0167 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor152

theorem floor151 : Floor 228 44 115034 := by
  have suffix : Floor 230 44 115034 :=
    weaken (by decide) (by decide) floor152
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G05.bound0166 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor151

theorem floor150 : Floor 161 44 77356 := by
  have suffix : Floor 165 44 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor044
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks142758G05.bound0165 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor150

theorem floor149 : Floor 159 44 76424 := by
  have suffix : Floor 161 44 76424 :=
    weaken (by decide) (by decide) floor150
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G05.bound0164 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor149

theorem floor148 : Floor 230 43 113448 := by
  have suffix : Floor 238 43 113448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor042
  intro s hs hbig
  by_cases h : s < 238
  · exact SourceCoverChecks142758G05.bound0163 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor148

theorem floor147 : Floor 228 43 109544 := by
  have suffix : Floor 230 43 109544 :=
    weaken (by decide) (by decide) floor148
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G05.bound0162 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor147

theorem floor146 : Floor 230 42 107584 := by
  have suffix : Floor 236 42 107584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor043
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks142758G05.bound0161 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor146

theorem floor145 : Floor 182 42 81413 := by
  have suffix : Floor 214 42 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor096
  intro s hs hbig
  by_cases h : s < 214
  · exact SourceCoverChecks142758G05.bound0160 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor145

theorem floor144 : Floor 161 42 71302 := by
  have suffix : Floor 163 42 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor049
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G04.bound0159 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor144

theorem floor143 : Floor 115 42 45761 := by
  have suffix : Floor 153 42 45761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor088
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks142758G04.bound0158 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor143

theorem floor142 : Floor 228 41 103808 := by
  have suffix : Floor 232 41 103808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor337
  intro s hs hbig
  by_cases h : s < 232
  · exact SourceCoverChecks142758G04.bound0157 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor142

theorem floor141 : Floor 159 41 68392 := by
  have suffix : Floor 163 41 68392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor012
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G04.bound0156 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor141

theorem floor140 : Floor 114 41 44842 := by
  have suffix : Floor 153 41 44842 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor088
  intro s hs hbig
  by_cases h : s < 153
  · exact SourceCoverChecks142758G04.bound0155 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor140

theorem floor139 : Floor 228 40 99186 := by
  have suffix : Floor 239 40 99186 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor332
  intro s hs hbig
  by_cases h : s < 239
  · exact SourceCoverChecks142758G04.bound0154 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor139

theorem floor138 : Floor 260 39 108096 := by
  have suffix : Floor 280 39 108096 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor092
  intro s hs hbig
  by_cases h : s < 280
  · exact SourceCoverChecks142758G04.bound0153 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor138

theorem floor137 : Floor 228 39 94250 := by
  have suffix : Floor 234 39 94250 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor048
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G04.bound0152 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor137

theorem floor136 : Floor 161 39 63298 := by
  have suffix : Floor 165 39 63298 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor041
  intro s hs hbig
  by_cases h : s < 165
  · exact SourceCoverChecks142758G04.bound0151 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor136

theorem floor135 : Floor 228 38 89288 := by
  have suffix : Floor 244 38 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor083
  intro s hs hbig
  by_cases h : s < 244
  · exact SourceCoverChecks142758G04.bound0150 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor135

theorem floor134 : Floor 161 38 59197 := by
  have suffix : Floor 180 38 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor072
  intro s hs hbig
  by_cases h : s < 180
  · exact SourceCoverChecks142758G04.bound0149 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor134

theorem floor133 : Floor 159 38 57486 := by
  have suffix : Floor 161 38 57486 :=
    weaken (by decide) (by decide) floor134
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G04.bound0148 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor133

theorem floor132 : Floor 228 37 84792 := by
  have suffix : Floor 234 37 84792 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor011
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G04.bound0147 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor132

theorem floor131 : Floor 345 36 123786 := by
  have suffix : Floor 351 36 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor046
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G04.bound0146 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor131

theorem floor130 : Floor 161 36 54629 := by
  have suffix : Floor 168 36 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor080
  intro s hs hbig
  by_cases h : s < 168
  · exact SourceCoverChecks142758G04.bound0145 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor130

theorem floor129 : Floor 159 36 52444 := by
  have suffix : Floor 161 36 52444 :=
    weaken (by decide) (by decide) floor130
  intro s hs hbig
  by_cases h : s < 161
  · exact SourceCoverChecks142758G04.bound0144 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor129

theorem floor128 : Floor 342 35 119702 := by
  have suffix : Floor 351 35 119702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor044
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G04.bound0143 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor128

theorem floor127 : Floor 230 35 77356 := by
  have suffix : Floor 236 35 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor038
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks142758G04.bound0142 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor127

theorem floor126 : Floor 228 35 76424 := by
  have suffix : Floor 230 35 76424 :=
    weaken (by decide) (by decide) floor127
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G04.bound0141 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor126

theorem floor125 : Floor 130 35 39469 := by
  have suffix : Floor 150 35 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor084
  intro s hs hbig
  by_cases h : s < 150
  · exact SourceCoverChecks142758G04.bound0140 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor125

theorem floor124 : Floor 345 34 113448 := by
  have suffix : Floor 357 34 113448 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor034
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks142758G04.bound0139 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor124

theorem floor123 : Floor 342 34 109544 := by
  have suffix : Floor 345 34 109544 :=
    weaken (by decide) (by decide) floor124
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G04.bound0138 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor123

theorem floor122 : Floor 260 34 81413 := by
  have suffix : Floor 302 34 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor249
  intro s hs hbig
  by_cases h : s < 302
  · exact SourceCoverChecks142758G04.bound0137 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor122

theorem floor121 : Floor 230 34 71302 := by
  have suffix : Floor 234 34 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor041
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G04.bound0136 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor121

theorem floor120 : Floor 115 34 32306 := by
  have suffix : Floor 117 34 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor040
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G04.bound0135 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor120

theorem floor119 : Floor 114 34 31702 := by
  have suffix : Floor 115 34 31702 :=
    weaken (by decide) (by decide) floor120
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G04.bound0134 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor119

theorem floor118 : Floor 345 33 107584 := by
  have suffix : Floor 354 33 107584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor035
  intro s hs hbig
  by_cases h : s < 354
  · exact SourceCoverChecks142758G04.bound0133 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor118

theorem floor117 : Floor 228 33 68392 := by
  have suffix : Floor 234 33 68392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor009
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G04.bound0132 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor117

theorem floor116 : Floor 342 32 99186 := by
  have suffix : Floor 357 32 99186 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors155716.floor033
  intro s hs hbig
  by_cases h : s < 357
  · exact SourceCoverChecks142758G04.bound0131 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor116

theorem floor115 : Floor 230 32 63298 := by
  have suffix : Floor 236 32 63298 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor033
  intro s hs hbig
  by_cases h : s < 236
  · exact SourceCoverChecks142758G04.bound0130 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor115

theorem floor114 : Floor 390 31 108096 := by
  have suffix : Floor 420 31 108096 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor074
  intro s hs hbig
  by_cases h : s < 420
  · exact SourceCoverChecks142758G04.bound0129 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor114

theorem floor113 : Floor 342 31 94250 := by
  have suffix : Floor 351 31 94250 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor038
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G04.bound0128 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor113

theorem floor112 : Floor 230 31 59197 := by
  have suffix : Floor 234 31 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor037
  intro s hs hbig
  by_cases h : s < 234
  · exact SourceCoverChecks142758G03.bound0127 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor112

theorem floor111 : Floor 345 30 88100 := by
  have suffix : Floor 366 30 88100 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor069
  intro s hs hbig
  by_cases h : s < 366
  · exact SourceCoverChecks142758G03.bound0126 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor111

theorem floor110 : Floor 342 30 84792 := by
  have suffix : Floor 345 30 84792 :=
    weaken (by decide) (by decide) floor111
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G03.bound0125 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor110

theorem floor109 : Floor 228 30 57486 := by
  have suffix : Floor 254 30 57486 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor058
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks142758G03.bound0124 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor109

theorem floor108 : Floor 345 29 83568 := by
  have suffix : Floor 351 29 83568 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor008
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G03.bound0123 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor108

theorem floor107 : Floor 230 29 54629 := by
  have suffix : Floor 240 29 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor066
  intro s hs hbig
  by_cases h : s < 240
  · exact SourceCoverChecks142758G03.bound0122 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor107

theorem floor106 : Floor 228 29 52444 := by
  have suffix : Floor 230 29 52444 :=
    weaken (by decide) (by decide) floor107
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G03.bound0121 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor106

theorem floor105 : Floor 345 28 77356 := by
  have suffix : Floor 354 28 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor030
  intro s hs hbig
  by_cases h : s < 354
  · exact SourceCoverChecks142758G03.bound0120 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor105

theorem floor104 : Floor 342 28 76424 := by
  have suffix : Floor 345 28 76424 :=
    weaken (by decide) (by decide) floor105
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G03.bound0119 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor104

theorem floor103 : Floor 182 28 39469 := by
  have suffix : Floor 210 28 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor063
  intro s hs hbig
  by_cases h : s < 210
  · exact SourceCoverChecks142758G03.bound0118 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor103

theorem floor102 : Floor 159 28 31702 := by
  have suffix : Floor 163 28 31702 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor034
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G03.bound0117 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor102

theorem floor101 : Floor 575 27 123786 := by
  have suffix : Floor 585 27 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor033
  intro s hs hbig
  by_cases h : s < 585
  · exact SourceCoverChecks142758G03.bound0116 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor101

theorem floor100 : Floor 570 27 119702 := by
  have suffix : Floor 575 27 119702 :=
    weaken (by decide) (by decide) floor101
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G03.bound0115 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor100

theorem floor099 : Floor 390 27 81413 := by
  have suffix : Floor 432 27 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor182
  intro s hs hbig
  by_cases h : s < 432
  · exact SourceCoverChecks142758G03.bound0114 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor099

theorem floor098 : Floor 345 27 71302 := by
  have suffix : Floor 351 27 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor032
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G03.bound0113 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor098

theorem floor097 : Floor 342 27 68392 := by
  have suffix : Floor 345 27 68392 :=
    weaken (by decide) (by decide) floor098
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G03.bound0112 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor097

theorem floor096 : Floor 230 27 45761 := by
  have suffix : Floor 306 27 45761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor049
  intro s hs hbig
  by_cases h : s < 306
  · exact SourceCoverChecks142758G03.bound0111 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor096

theorem floor095 : Floor 228 27 44842 := by
  have suffix : Floor 230 27 44842 :=
    weaken (by decide) (by decide) floor096
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G03.bound0110 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor095

theorem floor094 : Floor 161 27 32306 := by
  have suffix : Floor 177 27 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor051
  intro s hs hbig
  by_cases h : s < 177
  · exact SourceCoverChecks142758G03.bound0109 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor094

theorem floor093 : Floor 570 26 115034 := by
  have suffix : Floor 590 26 115034 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor028
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks142758G03.bound0108 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor093

theorem floor092 : Floor 345 26 63298 := by
  have suffix : Floor 351 26 63298 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor006
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G03.bound0107 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor092

theorem floor091 : Floor 661 25 123786 := by
  have suffix : Floor 670 25 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors200000.floor058
  intro s hs hbig
  by_cases h : s < 670
  · exact SourceCoverChecks142758G03.bound0106 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor091

theorem floor090 : Floor 575 25 107584 := by
  have suffix : Floor 590 25 107584 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor027
  intro s hs hbig
  by_cases h : s < 590
  · exact SourceCoverChecks142758G03.bound0105 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor090

theorem floor089 : Floor 570 25 103808 := by
  have suffix : Floor 575 25 103808 :=
    weaken (by decide) (by decide) floor090
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G03.bound0104 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor089

theorem floor088 : Floor 345 25 59197 := by
  have suffix : Floor 351 25 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor028
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G03.bound0103 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor088

theorem floor087 : Floor 342 25 57486 := by
  have suffix : Floor 345 25 57486 :=
    weaken (by decide) (by decide) floor088
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G03.bound0102 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor087

theorem floor086 : Floor 606 24 103808 := by
  have suffix : Floor 610 24 103808 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor027
  intro s hs hbig
  by_cases h : s < 610
  · exact SourceCoverChecks142758G03.bound0101 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor086

theorem floor085 : Floor 603 24 102866 := by
  have suffix : Floor 606 24 102866 :=
    weaken (by decide) (by decide) floor086
  intro s hs hbig
  by_cases h : s < 606
  · exact SourceCoverChecks142758G03.bound0100 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor085

theorem floor084 : Floor 593 24 99186 := by
  have suffix : Floor 598 24 99186 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor050
  intro s hs hbig
  by_cases h : s < 598
  · exact SourceCoverChecks142758G03.bound0099 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor084

theorem floor083 : Floor 575 24 97810 := by
  have suffix : Floor 593 24 97810 :=
    weaken (by decide) (by decide) floor084
  intro s hs hbig
  by_cases h : s < 593
  · exact SourceCoverChecks142758G03.bound0098 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor083

theorem floor082 : Floor 570 24 94250 := by
  have suffix : Floor 575 24 94250 :=
    weaken (by decide) (by decide) floor083
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G03.bound0097 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor082

theorem floor081 : Floor 345 24 54629 := by
  have suffix : Floor 350 24 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor148
  intro s hs hbig
  by_cases h : s < 350
  · exact SourceCoverChecks142758G03.bound0096 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor081

theorem floor080 : Floor 563 23 89288 := by
  have suffix : Floor 635 23 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor047
  intro s hs hbig
  by_cases h : s < 635
  · exact SourceCoverChecks142758G02.bound0095 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor080

theorem floor079 : Floor 559 23 88100 := by
  have suffix : Floor 563 23 88100 :=
    weaken (by decide) (by decide) floor080
  intro s hs hbig
  by_cases h : s < 563
  · exact SourceCoverChecks142758G02.bound0094 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor079

theorem floor078 : Floor 549 23 84792 := by
  have suffix : Floor 552 23 84792 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor005
  intro s hs hbig
  by_cases h : s < 552
  · exact SourceCoverChecks142758G02.bound0093 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor078

theorem floor077 : Floor 538 23 81413 := by
  have suffix : Floor 539 23 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor025
  intro s hs hbig
  by_cases h : s < 539
  · exact SourceCoverChecks142758G02.bound0092 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor077

theorem floor076 : Floor 525 23 77356 := by
  have suffix : Floor 535 23 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor024
  intro s hs hbig
  by_cases h : s < 535
  · exact SourceCoverChecks142758G02.bound0091 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor076

theorem floor075 : Floor 522 23 76424 := by
  have suffix : Floor 525 23 76424 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor004
  intro s hs hbig
  by_cases h : s < 525
  · exact SourceCoverChecks142758G02.bound0090 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor075

theorem floor074 : Floor 342 23 52444 := by
  have suffix : Floor 350 23 52444 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors291012.floor148
  intro s hs hbig
  by_cases h : s < 350
  · exact SourceCoverChecks142758G02.bound0089 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor074

theorem floor073 : Floor 260 23 39469 := by
  have suffix : Floor 300 23 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor048
  intro s hs hbig
  by_cases h : s < 300
  · exact SourceCoverChecks142758G02.bound0088 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor073

theorem floor072 : Floor 504 22 71302 := by
  have suffix : Floor 509 22 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor023
  intro s hs hbig
  by_cases h : s < 509
  · exact SourceCoverChecks142758G02.bound0087 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor072

theorem floor071 : Floor 494 22 68392 := by
  have suffix : Floor 496 22 68392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor003
  intro s hs hbig
  by_cases h : s < 496
  · exact SourceCoverChecks142758G02.bound0086 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor071

theorem floor070 : Floor 345 22 45761 := by
  have suffix : Floor 434 22 45761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor021
  intro s hs hbig
  by_cases h : s < 434
  · exact SourceCoverChecks142758G02.bound0085 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor070

theorem floor069 : Floor 230 22 32306 := by
  have suffix : Floor 254 22 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor042
  intro s hs hbig
  by_cases h : s < 254
  · exact SourceCoverChecks142758G02.bound0084 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor069

theorem floor068 : Floor 228 22 31702 := by
  have suffix : Floor 230 22 31702 :=
    weaken (by decide) (by decide) floor069
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G02.bound0083 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor068

theorem floor067 : Floor 461 21 59197 := by
  have suffix : Floor 472 21 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor022
  intro s hs hbig
  by_cases h : s < 472
  · exact SourceCoverChecks142758G02.bound0082 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor067

theorem floor066 : Floor 454 21 57486 := by
  have suffix : Floor 461 21 57486 :=
    weaken (by decide) (by decide) floor067
  intro s hs hbig
  by_cases h : s < 461
  · exact SourceCoverChecks142758G02.bound0081 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor066

theorem floor065 : Floor 443 21 54629 := by
  have suffix : Floor 447 21 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor040
  intro s hs hbig
  by_cases h : s < 447
  · exact SourceCoverChecks142758G02.bound0080 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor065

theorem floor064 : Floor 434 21 52444 := by
  have suffix : Floor 438 21 52444 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors153080.floor021
  intro s hs hbig
  by_cases h : s < 438
  · exact SourceCoverChecks142758G02.bound0079 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor064

theorem floor063 : Floor 342 21 44842 := by
  have suffix : Floor 434 21 44842 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor021
  intro s hs hbig
  by_cases h : s < 434
  · exact SourceCoverChecks142758G02.bound0078 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor063

theorem floor062 : Floor 115 21 13520 := by
  have suffix : Floor 117 21 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor020
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G02.bound0077 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor062

theorem floor061 : Floor 114 21 13285 := by
  have suffix : Floor 115 21 13285 :=
    weaken (by decide) (by decide) floor062
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G02.bound0076 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor061

theorem floor060 : Floor 406 20 45761 := by
  have suffix : Floor 459 20 45761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor033
  intro s hs hbig
  by_cases h : s < 459
  · exact SourceCoverChecks142758G02.bound0075 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor060

theorem floor059 : Floor 402 20 44842 := by
  have suffix : Floor 406 20 44842 :=
    weaken (by decide) (by decide) floor060
  intro s hs hbig
  by_cases h : s < 406
  · exact SourceCoverChecks142758G02.bound0074 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor059

theorem floor058 : Floor 378 19 39469 := by
  have suffix : Floor 450 19 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor031
  intro s hs hbig
  by_cases h : s < 450
  · exact SourceCoverChecks142758G02.bound0073 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor058

theorem floor057 : Floor 343 18 32306 := by
  have suffix : Floor 350 18 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor019
  intro s hs hbig
  by_cases h : s < 350
  · exact SourceCoverChecks142758G02.bound0072 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor057

theorem floor056 : Floor 340 18 31702 := by
  have suffix : Floor 343 18 31702 :=
    weaken (by decide) (by decide) floor057
  intro s hs hbig
  by_cases h : s < 343
  · exact SourceCoverChecks142758G02.bound0071 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor056

theorem floor055 : Floor 161 18 13520 := by
  have suffix : Floor 163 18 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor018
  intro s hs hbig
  by_cases h : s < 163
  · exact SourceCoverChecks142758G02.bound0070 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor055

theorem floor054 : Floor 1150 17 92724 := by
  have suffix : Floor 1170 17 92724 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor017
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G02.bound0069 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor054

theorem floor053 : Floor 159 17 13285 := by
  have suffix : Floor 224 17 13285 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor015
  intro s hs hbig
  by_cases h : s < 224
  · exact SourceCoverChecks142758G02.bound0068 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor053

theorem floor052 : Floor 1140 16 89288 := by
  have suffix : Floor 1220 16 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor033
  intro s hs hbig
  by_cases h : s < 1220
  · exact SourceCoverChecks142758G02.bound0067 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor052

theorem floor051 : Floor 1150 15 77356 := by
  have suffix : Floor 1170 15 77356 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor016
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G02.bound0066 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor051

theorem floor050 : Floor 1140 15 76424 := by
  have suffix : Floor 1150 15 76424 :=
    weaken (by decide) (by decide) floor051
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G02.bound0065 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor050

theorem floor049 : Floor 650 15 39469 := by
  have suffix : Floor 750 15 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor020
  intro s hs hbig
  by_cases h : s < 750
  · exact SourceCoverChecks142758G02.bound0064 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor049

theorem floor048 : Floor 219 15 13520 := by
  have suffix : Floor 224 15 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor015
  intro s hs hbig
  by_cases h : s < 224
  · exact SourceCoverChecks142758G01.bound0063 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor048

theorem floor047 : Floor 218 15 13285 := by
  have suffix : Floor 219 15 13285 :=
    weaken (by decide) (by decide) floor048
  intro s hs hbig
  by_cases h : s < 219
  · exact SourceCoverChecks142758G01.bound0062 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor047

theorem floor046 : Floor 115 15 7057 := by
  have suffix : Floor 218 15 7057 :=
    weaken (by decide) (by decide) floor047
  intro s hs hbig
  by_cases h : s < 218
  · exact SourceCoverChecks142758G01.bound0061 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor046

theorem floor045 : Floor 114 15 6938 := by
  have suffix : Floor 115 15 6938 :=
    weaken (by decide) (by decide) floor046
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G01.bound0060 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor045

theorem floor044 : Floor 1140 14 68392 := by
  have suffix : Floor 1170 14 68392 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors150465.floor001
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G01.bound0059 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor044

theorem floor043 : Floor 575 14 32306 := by
  have suffix : Floor 585 14 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor013
  intro s hs hbig
  by_cases h : s < 585
  · exact SourceCoverChecks142758G01.bound0058 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor043

theorem floor042 : Floor 570 14 31702 := by
  have suffix : Floor 575 14 31702 :=
    weaken (by decide) (by decide) floor043
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G01.bound0057 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor042

theorem floor041 : Floor 1150 13 59197 := by
  have suffix : Floor 1290 13 59197 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors180000.floor024
  intro s hs hbig
  by_cases h : s < 1290
  · exact SourceCoverChecks142758G01.bound0056 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor041

theorem floor040 : Floor 1140 13 57486 := by
  have suffix : Floor 1150 13 57486 :=
    weaken (by decide) (by decide) floor041
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G01.bound0055 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor040

theorem floor039 : Floor 160 13 7057 := by
  have suffix : Floor 351 13 7057 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor011
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G01.bound0054 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor039

theorem floor038 : Floor 1150 12 45761 := by
  have suffix : Floor 1170 12 45761 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor012
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G01.bound0053 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor038

theorem floor037 : Floor 1140 12 44842 := by
  have suffix : Floor 1150 12 44842 :=
    weaken (by decide) (by decide) floor038
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G01.bound0052 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor037

theorem floor036 : Floor 345 12 13520 := by
  have suffix : Floor 351 12 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor011
  intro s hs hbig
  by_cases h : s < 351
  · exact SourceCoverChecks142758G01.bound0051 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor036

theorem floor035 : Floor 342 12 13285 := by
  have suffix : Floor 345 12 13285 :=
    weaken (by decide) (by decide) floor036
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G01.bound0050 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor035

theorem floor034 : Floor 158 12 6938 := by
  have suffix : Floor 342 12 6938 :=
    weaken (by decide) (by decide) floor035
  intro s hs hbig
  by_cases h : s < 342
  · exact SourceCoverChecks142758G01.bound0049 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor034

theorem floor033 : Floor 3680 11 123786 := by
  have suffix : Floor 3744 11 123786 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor010
  intro s hs hbig
  by_cases h : s < 3744
  · exact SourceCoverChecks142758G01.bound0048 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor033

theorem floor032 : Floor 3648 11 119702 := by
  have suffix : Floor 3680 11 119702 :=
    weaken (by decide) (by decide) floor033
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G01.bound0047 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor032

theorem floor031 : Floor 1300 11 39469 := by
  have suffix : Floor 1500 11 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor007
  intro s hs hbig
  by_cases h : s < 1500
  · exact SourceCoverChecks142758G01.bound0046 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor031

theorem floor030 : Floor 130 11 4666 :=
  of_prefix_tail (C := 506) (by decide) (by decide) (by decide +kernel) SourceCoverChecks142758G01.bound0045
#print axioms floor030

theorem floor029 : Floor 115 11 3610 := by
  have suffix : Floor 117 11 3610 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor009
  intro s hs hbig
  by_cases h : s < 117
  · exact SourceCoverChecks142758G01.bound0044 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor029

theorem floor028 : Floor 114 11 3549 := by
  have suffix : Floor 115 11 3549 :=
    weaken (by decide) (by decide) floor029
  intro s hs hbig
  by_cases h : s < 115
  · exact SourceCoverChecks142758G01.bound0043 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor028

theorem floor027 : Floor 3648 10 109544 := by
  have suffix : Floor 3744 10 109544 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor008
  intro s hs hbig
  by_cases h : s < 3744
  · exact SourceCoverChecks142758G01.bound0042 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor027

theorem floor026 : Floor 1150 10 32306 := by
  have suffix : Floor 1170 10 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor007
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G01.bound0041 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor026

theorem floor025 : Floor 1140 10 31702 := by
  have suffix : Floor 1150 10 31702 :=
    weaken (by decide) (by decide) floor026
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G01.bound0040 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor025

theorem floor024 : Floor 230 10 7057 := by
  have suffix : Floor 585 10 7057 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor005
  intro s hs hbig
  by_cases h : s < 585
  · exact SourceCoverChecks142758G01.bound0039 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor024

theorem floor023 : Floor 228 10 6938 := by
  have suffix : Floor 230 10 6938 :=
    weaken (by decide) (by decide) floor024
  intro s hs hbig
  by_cases h : s < 230
  · exact SourceCoverChecks142758G01.bound0038 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor023

theorem floor022 : Floor 3648 9 89288 := by
  have suffix : Floor 3904 9 89288 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor010
  intro s hs hbig
  by_cases h : s < 3904
  · exact SourceCoverChecks142758G01.bound0037 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor022

theorem floor021 : Floor 575 9 13520 := by
  have suffix : Floor 585 9 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor005
  intro s hs hbig
  by_cases h : s < 585
  · exact SourceCoverChecks142758G01.bound0036 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor021

theorem floor020 : Floor 570 9 13285 := by
  have suffix : Floor 575 9 13285 :=
    weaken (by decide) (by decide) floor021
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G01.bound0035 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor020

theorem floor019 : Floor 345 9 7057 := by
  have suffix : Floor 570 9 7057 :=
    weaken (by decide) (by decide) floor020
  intro s hs hbig
  by_cases h : s < 570
  · exact SourceCoverChecks142758G01.bound0034 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor019

theorem floor018 : Floor 342 9 6938 := by
  have suffix : Floor 345 9 6938 :=
    weaken (by decide) (by decide) floor019
  intro s hs hbig
  by_cases h : s < 345
  · exact SourceCoverChecks142758G01.bound0033 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor018

theorem floor017 : Floor 4160 8 81413 := by
  have suffix : Floor 4896 8 81413 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor003
  intro s hs hbig
  by_cases h : s < 4896
  · exact join017_01 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor017

theorem floor016 : Floor 3680 8 71302 := by
  have suffix : Floor 3744 8 71302 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor004
  intro s hs hbig
  by_cases h : s < 3744
  · exact SourceCoverChecks142758G00.bound0029 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor016

theorem floor015 : Floor 3648 8 68392 := by
  have suffix : Floor 3680 8 68392 :=
    weaken (by decide) (by decide) floor016
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G00.bound0028 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor015

theorem floor014 : Floor 3680 7 54629 := by
  have suffix : Floor 3840 7 54629 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors158375.floor005
  intro s hs hbig
  by_cases h : s < 3840
  · exact SourceCoverChecks142758G00.bound0027 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor014

theorem floor013 : Floor 3648 7 52444 := by
  have suffix : Floor 3680 7 52444 :=
    weaken (by decide) (by decide) floor014
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G00.bound0026 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor013

theorem floor012 : Floor 1150 7 13520 := by
  have suffix : Floor 1170 7 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor002
  intro s hs hbig
  by_cases h : s < 1170
  · exact SourceCoverChecks142758G00.bound0025 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor012

theorem floor011 : Floor 1140 7 13285 := by
  have suffix : Floor 1150 7 13285 :=
    weaken (by decide) (by decide) floor012
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G00.bound0024 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor011

theorem floor010 : Floor 575 7 7057 := by
  have suffix : Floor 1140 7 7057 :=
    weaken (by decide) (by decide) floor011
  intro s hs hbig
  by_cases h : s < 1140
  · exact SourceCoverChecks142758G00.bound0023 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor010

theorem floor009 : Floor 570 7 6938 := by
  have suffix : Floor 575 7 6938 :=
    weaken (by decide) (by decide) floor010
  intro s hs hbig
  by_cases h : s < 575
  · exact SourceCoverChecks142758G00.bound0022 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor009

theorem floor008 : Floor 4160 6 39469 := by
  have suffix : Floor 4800 6 39469 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors250262.floor000
  intro s hs hbig
  by_cases h : s < 4800
  · exact join008_00 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor008

theorem floor007 : Floor 3680 6 32306 := by
  have suffix : Floor 3744 6 32306 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor001
  intro s hs hbig
  by_cases h : s < 3744
  · exact SourceCoverChecks142758G00.bound0019 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor007

theorem floor006 : Floor 3648 6 31702 := by
  have suffix : Floor 3680 6 31702 :=
    weaken (by decide) (by decide) floor007
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G00.bound0018 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor006

theorem floor005 : Floor 1150 5 7057 :=
  of_prefix_tail (C := 3299) (by decide) (by decide) (by decide +kernel) join005_02
#print axioms floor005

theorem floor004 : Floor 1140 5 6938 := by
  have suffix : Floor 1150 5 6938 :=
    weaken (by decide) (by decide) floor005
  intro s hs hbig
  by_cases h : s < 1150
  · exact SourceCoverChecks142758G00.bound0013 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor004

theorem floor003 : Floor 3680 4 13520 := by
  have suffix : Floor 3744 4 13520 :=
    floor_weaken_defect (by decide) (by decide) (by decide)
      SourceFloors151879.floor000
  intro s hs hbig
  by_cases h : s < 3744
  · exact SourceCoverChecks142758G00.bound0012 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor003

theorem floor002 : Floor 3648 4 13285 := by
  have suffix : Floor 3680 4 13285 :=
    weaken (by decide) (by decide) floor003
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G00.bound0011 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor002

theorem floor001 : Floor 3680 3 7057 :=
  of_prefix_tail (C := 8237) (by decide) (by decide) (by decide +kernel) join001_08
#print axioms floor001

theorem floor000 : Floor 3648 3 6938 := by
  have suffix : Floor 3680 3 6938 :=
    weaken (by decide) (by decide) floor001
  intro s hs hbig
  by_cases h : s < 3680
  · exact SourceCoverChecks142758G00.bound0000 s hs h
  · exact suffix s (by omega) hbig
#print axioms floor000

end JSP233.SourceFloors142758
